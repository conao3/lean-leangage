"""The engine's contract, item by item (the numbers of the list in `leangage/pg/__init__.py`),
against the test process's PostgreSQL with injected faults: forced serialization failures and
deadlocks, terminated backends, COMMITs lost before or after the server ran them, a client that
stops waiting, other engines writing the same tenant, and many concurrent clients. Each test has
a database of its own."""

import socket
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from typing import Any

import psycopg
import pytest
from leanfran import Ok
from leangage import (
    Api,
    Broken,
    Claims,
    CommitUnknown,
    EngineError,
    IdempotencyConflict,
    Refused,
    RetriesExhausted,
    http_format,
    issue,
    json_lexemes,
    serve,
)
from leangage.pg import Attempt, Config, PgEngine, Point, lockdown
from leangage.pg.testing import ENGINE_ROLE, OWNER, cluster, connect
from pg_common import (
    CELLS,
    NEGATIVE,
    Actor,
    Add,
    Db,
    Fault,
    Get,
    Move,
    Outcome,
    Poke,
    Proxy,
    actor,
    admin_connection,
    config,
    hook_at,
    kill,
    setup,
)

T = 30.0


def in_time(f: Any, *args: Any) -> Any:
    """`f(*args)`, which must return or raise `Refused` or an `EngineError` within `T` seconds.
    It runs on a daemon thread, so a call that hangs fails the test and not the process's exit."""
    box: dict[str, Any] = {}

    def target() -> None:
        try:
            box["value"] = f(*args)
        except (Refused, EngineError) as e:
            box["error"] = e

    thread = threading.Thread(target=target, daemon=True)
    thread.start()
    thread.join(T)
    assert not thread.is_alive(), "in time"
    if "error" in box:
        raise box["error"]
    assert "value" in box, "returned"
    return box["value"]


def run(engine: PgEngine, tenant: int, cmd: Any) -> Any:
    return in_time(engine.execute, actor(tenant), cmd)


def run_keyed(engine: PgEngine, tenant: int, key: str, cmd: Any) -> Any:
    return in_time(
        engine.execute_idempotent, actor(tenant), "u1", key, repr(cmd).encode(), cmd
    )


def outcome(f: Any, *args: Any) -> Any:
    """The reply, the refusal or the engine's error of `f(*args)`."""
    try:
        return f(*args)
    except Refused as e:
        return ("refused", e.error)
    except EngineError as e:
        return type(e)


def conflict(db: Db, tenant: int) -> None:
    """An outside transaction that changes cell 0 of `tenant` after the attempt's snapshot, and
    advances the tenant's version as an engine's commit does."""
    db.one(
        "WITH u AS (UPDATE cells SET v = v + 100 WHERE tenant_id = $1 AND id = 0 RETURNING 1), "
        "w AS (INSERT INTO leangage_version (tenant_id, version) SELECT $1, 1 FROM u "
        "ON CONFLICT (tenant_id) DO UPDATE SET version = leangage_version.version + 1 "
        "RETURNING 1) SELECT count(*) FROM w",
        [tenant],
    )


# Items 1 and 2: one attempt is one SERIALIZABLE read-write transaction; a retry is a new
# transaction that reads the rows again and calls `transition` again.
def test_serialization_failures_retry_in_a_new_transaction() -> None:
    db = setup("contract_ssi")
    hook, seen = hook_at(Point.LOADED, 2, lambda a: conflict(db, a.tenant))
    plain = db.engine(1)
    run(plain, 1, Add(0, 5))
    pg = db.engine(2, config(20, True, hook))
    r = run(pg, 1, Add(0, 1))
    assert pg.stats.attempts == 3
    assert pg.stats.retries == 2
    # Each retry read the outside commits made after the snapshot of the attempt before it.
    assert r == 5 + 100 + 100 + 1
    assert db.cell(1, 0) == 206
    txs = [a.tx for a in seen.at(Point.LOADED)]
    assert len(txs) == 3
    for tx in txs:
        assert tx is not None
        assert tx.isolation == "serializable"
        assert not tx.read_only
    assert len({tx.vxid for tx in txs if tx is not None}) == 3


# Item 2: retries stop after `max_attempts` with `RetriesExhausted`, and no attempt left a write
# or a stored reply.
def test_serialization_failures_exhaust_after_max_attempts() -> None:
    db = setup("contract_exhaust")
    hook, _ = hook_at(Point.LOADED, float("inf"), lambda a: conflict(db, a.tenant))
    plain = db.engine(1)
    run(plain, 1, Add(0, 5))
    pg = db.engine(2, config(3, True, hook))
    assert outcome(run_keyed, pg, 1, "k", Add(0, 1)) is RetriesExhausted
    assert pg.stats.attempts == 3
    assert db.cell(1, 0) == 305, "only the outside writes"
    assert db.replies(1) == 0


# Item 2 (deadlock): the attempt holds the tenant's advisory lock and waits for a row an outside
# transaction holds, which then waits for the advisory lock. PostgreSQL aborts the attempt with
# 40P01 (the outside session waits 30 s before it checks), and the retry succeeds.
def test_deadlocks_are_retried() -> None:
    db = setup("contract_deadlock")
    other = admin_connection(db)
    outside: list[threading.Thread] = []
    failures: list[BaseException] = []

    def wait_and_lock(a: Attempt) -> None:
        try:
            while (
                db.one(
                    "SELECT count(*) FROM pg_locks WHERE pid = $1 AND NOT granted",
                    [a.pid],
                )
                == 0
            ):
                time.sleep(0.005)
            other.execute("SELECT pg_advisory_xact_lock($1::bigint)", [a.tenant])
            other.execute("ROLLBACK")
        except (psycopg.Error, AssertionError) as e:
            failures.append(e)

    def f(a: Attempt) -> None:
        other.execute("BEGIN")
        other.execute("SET LOCAL deadlock_timeout = '30s'")
        other.execute(
            "UPDATE cells SET v = v WHERE tenant_id = $1 AND id = 0", [a.tenant]
        )
        thread = threading.Thread(target=wait_and_lock, args=(a,))
        thread.start()
        outside.append(thread)

    hook, _ = hook_at(Point.LOADED, 1, f)
    pg = db.engine(2, config(20, True, hook))
    plain = db.engine(1)
    run(plain, 1, Add(0, 5))
    r = run(pg, 1, Add(0, 1))
    outside[0].join(T)
    assert not failures
    assert pg.stats.retries == 1, "one retry, after the deadlock"
    assert r == 6
    assert db.cell(1, 0) == 6
    assert db.no_advisory_locks(2) == 0


# Item 2 (lost connection): a backend terminated before COMMIT (at each point of an attempt)
# retries from BEGIN on a new connection, and the command takes effect once, with or without a
# key. Without a key, a connection lost right before COMMIT and noticed only by COMMIT is
# `CommitUnknown` (it did not commit; the engine cannot know that).
def test_killed_before_commit_retries_once() -> None:
    db = setup("contract_kill")
    tenant = 0
    for point in [Point.LOCKED, Point.LOADED, Point.WRITTEN]:
        for keyed in [False, True]:
            tenant += 1
            hook, seen = hook_at(point, 1, lambda a: kill(db, a.pid))
            pg = db.engine(2, config(20, True, hook))
            cmd = Add(0, 7)
            if keyed:
                r = outcome(run_keyed, pg, tenant, "k", cmd)
            else:
                r = outcome(run, pg, tenant, cmd)
            case = f"{point}, keyed {keyed}"
            if point == Point.WRITTEN and not keyed:
                assert r is CommitUnknown, case
                assert db.cell(tenant, 0) is None, f"{case}: not committed"
            else:
                assert r == 7, case
                assert db.cell(tenant, 0) == 7, f"{case}: once"
                assert pg.stats.retries == 1, f"{case}: one retry"
                pids = [a.pid for a in seen.at(point)]
                assert len(pids) == 2, case
                assert pids[0] != pids[1], f"{case}: a new connection"
            assert db.replies(tenant) == int(keyed and r == 7), case
    assert db.no_advisory_locks(2) == 0


# Item 3: a refused command rolls back and stores no row and no reply, with or without a key.
def test_refusals_write_nothing() -> None:
    db = setup("contract_refusal")
    pg = db.engine(2)
    run(pg, 1, Add(0, 5))
    before = pg.stats.commits
    assert outcome(run, pg, 1, Add(0, -10)) == ("refused", NEGATIVE)
    assert outcome(run_keyed, pg, 1, "k", Add(0, -10)) == ("refused", NEGATIVE)
    assert outcome(run, pg, 1, Move(0, 1, 50)) == ("refused", NEGATIVE)
    assert pg.stats.commits == before, "no commit"
    assert db.cells(1) == {0: 5}
    assert db.replies(1) == 0
    # The refusal stored no reply under its key: the same command runs again once it is
    # accepted.
    run(pg, 1, Add(0, 20))
    assert run_keyed(pg, 1, "k", Add(0, -10)) == 15
    assert db.replies(1) == 1


# Item 4: the app's writes and the stored reply commit together. A COMMIT lost before the
# server ran it leaves neither; one lost after the server committed leaves both.
def test_replies_commit_with_the_writes() -> None:
    db = setup("contract_atomic")
    proxy = Proxy(cluster())
    pg = db.engine_at(proxy.url(db.name), 1, config(1, True, None))
    proxy.arm(Fault.DROP_BEFORE)
    r = outcome(run_keyed, pg, 1, "a", Add(0, 3))
    assert r is RetriesExhausted, "one attempt, COMMIT lost"
    assert db.cell(1, 0) is None
    assert db.replies(1) == 0
    proxy.arm(Fault.DROP_AFTER)
    r = outcome(run_keyed, pg, 2, "a", Add(0, 3))
    assert r is RetriesExhausted, "one attempt, COMMIT lost"
    assert db.cell(2, 0) == 3
    assert db.replies(2) == 1
    assert proxy.outcomes() == [Outcome.NOT_SENT, Outcome.COMMITTED]


# Item 4: a reply is stored per tenant, scope and key; the same key with the same command
# replays it without running the command, and with another command is refused.
def test_idempotency_keys_replay_and_conflict() -> None:
    db = setup("contract_keys")
    pg = db.engine(2)
    assert run_keyed(pg, 1, "k", Add(0, 2)) == 2
    assert run_keyed(pg, 1, "k", Add(0, 2)) == 2
    assert pg.stats.replays == 1, "one replay"
    assert db.cell(1, 0) == 2, "ran once"
    assert outcome(run_keyed, pg, 1, "k", Add(0, 3)) is IdempotencyConflict
    cmd = Add(0, 2)
    r = pg.execute_idempotent(actor(1), "u2", "k", repr(cmd).encode(), cmd)
    assert r == 4, "another scope runs the command"
    assert run_keyed(pg, 2, "k", Add(0, 3)) == 3, "another tenant"
    assert db.cell(1, 0) == 4
    assert db.replies(1) == 2


# Item 4: concurrent requests with one key run the command once; the others replay its reply
# (a loser of the race for the key's row gets 23505 and retries).
def test_concurrent_requests_with_one_key_run_once() -> None:
    db = setup("contract_one_key")
    for tenant, lock in [(1, True), (2, False)]:
        pg = db.engine(8, config(20, lock, None))
        with ThreadPoolExecutor(32) as pool:
            futures = [
                pool.submit(run_keyed, pg, tenant, "once", Add(0, 1)) for _ in range(32)
            ]
            replies = [f.result() for f in futures]
        assert replies == [1] * 32, f"lock {lock}"
        assert db.cell(tenant, 0) == 1, f"lock {lock}"
        assert db.replies(tenant) == 1
        assert pg.stats.commits == 1, "one commit"
        assert pg.stats.replays == 31, "31 replays"


# Item 5: the tenant's advisory lock is held from before BEGIN to before the connection returns
# to the pool. A request queued behind it waits in `pg_advisory_lock` before its transaction, so
# it reads the first request's commit and commits without a retry.
def test_advisory_lock_is_held_around_the_transaction() -> None:
    db = setup("contract_lock")
    release = threading.Event()
    held: list[int] = []

    def f(a: Attempt) -> None:
        held.append(
            db.one(
                "SELECT count(*) FROM pg_locks WHERE locktype = 'advisory' AND granted "
                "AND pid = $1 AND objid::bigint = $2",
                [a.pid, a.tenant],
            )
        )
        release.wait(T)

    hook, _ = hook_at(Point.WRITTEN, 1, f)
    pg = db.engine(2, config(20, True, hook))
    with ThreadPoolExecutor(2) as pool:
        first = pool.submit(run, pg, 1, Add(0, 1))
        while not held:
            time.sleep(0.005)
        assert held[0] == 1, "the lock is held before COMMIT"
        second = pool.submit(run, pg, 1, Add(0, 10))
        deadline = time.monotonic() + T
        while True:
            with db._lock:
                row = db.admin.execute(
                    "SELECT l.pid FROM pg_locks l JOIN pg_stat_activity a ON a.pid = l.pid "
                    "WHERE l.locktype = 'advisory' AND NOT l.granted AND a.query = $1 "
                    "AND a.datname = current_database()",
                    ["SELECT pg_advisory_lock($1)"],
                ).fetchone()
            if row is not None:
                waiting = row[0]
                break
            assert time.monotonic() < deadline
            time.sleep(0.005)
        # The waiting request has not read the table: it holds no lock on it, not even the
        # predicate lock of a SERIALIZABLE read.
        read = db.one(
            "SELECT count(*) FROM pg_locks WHERE pid = $1 AND relation = 'cells'::regclass",
            [waiting],
        )
        assert read == 0
        release.set()
        assert first.result(T) == 1
        assert second.result(T) == 11, "it read the first commit"
    assert pg.stats.retries == 0, "no retry"
    assert db.no_advisory_locks(2) == 0


@dataclass(frozen=True)
class Call:
    actor: Actor
    cmd: Add


def cells_api() -> Api:
    def request(tenant: int, user: int, expiry: int, now: int, body: Any) -> Any:
        cell, delta = (
            int(token.text)
            for token in json_lexemes.unpack(body.packed)
            if isinstance(token, json_lexemes.Lexeme_number)
        )
        return Ok(value=Call(Actor(tenant, user), Add(cell, delta)))

    def respond(decision: Any) -> http_format.Response:
        if isinstance(decision, Ok):
            return http_format.Response(
                status=200, body=list(str(decision.value).encode())
            )
        return http_format.Response(status=422, body=list(decision.error.encode()))

    return Api(
        request=request,
        respond=respond,
        fingerprint=lambda cmd: repr(cmd).encode(),
        scope=lambda actor: f"u{actor.user}",
    )


# Item 5: no advisory lock is left after a commit, a refusal, an attempt whose backend was
# terminated, a failed request, or a client that stopped waiting; the pool keeps its connections
# and another engine gets the tenant at once.
def test_advisory_locks_are_released() -> None:
    db = setup("contract_release")
    hook, _ = hook_at(Point.LOADED, 1, lambda a: kill(db, a.pid))
    pg = db.engine(2, config(20, True, hook))
    run(pg, 1, Add(0, 5))
    assert db.no_advisory_locks(2) == 0, "killed"
    run(pg, 1, Add(0, 1))
    assert db.advisory_locks() == 0, "commit"
    assert outcome(run, pg, 1, Add(0, -100)) == ("refused", NEGATIVE)
    assert db.advisory_locks() == 0, "refusal"
    run_keyed(pg, 1, "k", Add(0, 1))
    assert outcome(run_keyed, pg, 1, "k", Add(0, 2)) is IdempotencyConflict
    assert db.advisory_locks() == 0, "failed request"

    # A client that closes its HTTP connection while its request waits before COMMIT.
    release = threading.Event()
    hook, seen = hook_at(Point.WRITTEN, 1, lambda _: release.wait(T))
    blocked = db.engine(2, config(20, True, hook))
    secret = b"secret"
    server = serve(blocked, cells_api(), secret, "127.0.0.1", 0)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    try:
        body = b'{"cell":0,"delta":100}'
        token = issue(secret, Claims(1, 1, int(time.time()) + 600))
        client = socket.create_connection(server.server_address[:2])
        client.sendall(
            b"POST /rpc HTTP/1.1\r\nHost: x\r\nAuthorization: Bearer "
            + token.encode()
            + b"\r\nContent-Length: "
            + str(len(body)).encode()
            + b"\r\n\r\n"
            + body
        )
        deadline = time.monotonic() + T
        while not seen.at(Point.WRITTEN):
            assert time.monotonic() < deadline
            time.sleep(0.005)
        client.close()
        release.set()
        assert db.no_advisory_locks(5) == 0, "dropped"
        # The request ran to its end on its thread: its command committed once.
        assert db.cell(1, 0) == 107
    finally:
        server.shutdown()
        server.server_close()
    other = db.engine(1, config(1, True, None))
    assert run(other, 1, Add(0, 1)) == 108, "the tenant is free"
    assert blocked.idle() == 1, "the connection is back in the pool"


# Item 6: a read-only command runs in one SERIALIZABLE READ ONLY DEFERRABLE transaction without
# the advisory lock, is retried after a lost connection, and fails if it writes; with a key it
# takes the write path.
def test_read_only_path() -> None:
    db = setup("contract_read")
    locks: list[int] = []

    def f(a: Attempt) -> None:
        locks.append(
            db.one(
                "SELECT count(*) FROM pg_locks WHERE locktype = 'advisory' AND pid = $1",
                [a.pid],
            )
        )

    hook, seen = hook_at(Point.LOADED, float("inf"), f)
    pg = db.engine(2, config(20, True, hook))
    run(pg, 1, Add(0, 5))
    before = pg.stats.reads
    assert run(pg, 1, Get(0)) == 5
    assert pg.stats.reads - before == 1, "one read"
    tx = seen.at(Point.LOADED)[-1].tx
    assert tx is not None
    assert tx.isolation == "serializable"
    assert tx.read_only and tx.deferrable
    assert locks[-1] == 0, "no advisory lock"
    assert len(seen.at(Point.LOCKED)) == 1, "only the write took the lock"

    # A command that claims to read only and writes fails, and nothing is stored.
    assert outcome(run, pg, 1, Poke(0)) is Broken
    assert db.cell(1, 0) == 5

    # With a key, a read takes the write path and stores its reply.
    before = pg.stats.reads
    assert run_keyed(pg, 1, "r", Get(0)) == 5
    assert pg.stats.reads == before, "not a read"
    keyed = seen.at(Point.LOADED)[-1].tx
    assert keyed is not None
    assert not keyed.read_only
    assert db.replies(1) == 1

    # A lost connection is retried.
    hook, seen = hook_at(Point.LOADED, 1, lambda a: kill(db, a.pid))
    killed = db.engine(2, config(20, True, hook))
    assert run(killed, 1, Get(0)) == 5
    assert killed.stats.reads == 2, "two reads"
    assert len(seen.at(Point.LOADED)) == 2


# Item 7: without a key, a COMMIT lost before or after the server ran it is `CommitUnknown`, not
# retried; the first did not commit and the second did. The proxy sees the COMMIT of each
# command on a connection that ran more commands than the driver runs before it prepares a
# statement.
def test_lost_commit_without_key_is_unknown() -> None:
    db = setup("contract_unknown")
    proxy = Proxy(cluster())
    pg = db.engine_at(proxy.url(db.name), 1, config(20, True, None))
    for i in range(10):
        assert run(pg, 3, Add(0, 1)) == i + 1
    proxy.arm(Fault.DROP_BEFORE)
    assert outcome(run, pg, 1, Add(0, 3)) is CommitUnknown
    proxy.arm(Fault.DROP_AFTER)
    assert outcome(run, pg, 2, Add(0, 3)) is CommitUnknown
    assert pg.stats.retries == 0, "not retried"
    assert db.cell(1, 0) is None
    assert db.cell(2, 0) == 3
    assert proxy.outcomes() == [Outcome.NOT_SENT, Outcome.COMMITTED]


# Item 7, with a key: a lost COMMIT is retried, and the command takes effect once; after a
# COMMIT the server ran, the retry replays the stored reply.
def test_lost_commit_with_key_runs_once() -> None:
    db = setup("contract_lost_keyed")
    proxy = Proxy(cluster())
    pg = db.engine_at(proxy.url(db.name), 1, config(20, True, None))
    proxy.arm(Fault.DROP_BEFORE)
    assert run_keyed(pg, 1, "k", Add(0, 3)) == 3
    proxy.arm(Fault.DROP_AFTER)
    assert run_keyed(pg, 2, "k", Add(0, 3)) == 3
    assert db.cell(1, 0) == 3
    assert db.cell(2, 0) == 3
    assert pg.stats.replays == 1, "the second replayed"
    assert proxy.outcomes() == [Outcome.NOT_SENT, Outcome.COMMITTED]


def mover(pg: PgEngine, tenant: int, c: int) -> list[tuple[int, int]]:
    """Eight moves of one unit around the four cells; the accepted ones."""
    moved = []
    for i in range(8):
        src, dst = (c + i) % 4, (c + i + 1) % 4
        try:
            pg.execute(actor(tenant), Move(src, dst, 1))
        except Refused:
            continue
        moved.append((src, dst))
    return moved


# With PostgreSQL's SERIALIZABLE, whose commits equal a serial order: 64 clients move units
# between four cells of one tenant, with and without the advisory lock. The total is kept, and
# each cell holds what the accepted moves left there.
def test_concurrent_moves_are_serial() -> None:
    db = setup("contract_serial")
    for tenant, lock in [(1, True), (2, False)]:
        pg = db.engine(8, config(1000, lock, None))
        for cell in range(4):
            run(pg, tenant, Add(cell, 100))

        with ThreadPoolExecutor(64) as pool:
            futures = [pool.submit(mover, pg, tenant, c) for c in range(64)]
            results = [f.result() for f in futures]
        expected = {0: 100, 1: 100, 2: 100, 3: 100}
        accepted = 0
        for moved in results:
            for src, dst in moved:
                expected[src] -= 1
                expected[dst] += 1
                accepted += 1
        assert accepted == 512, f"lock {lock}"
        assert db.cells(tenant) == expected, f"lock {lock}"
        if lock:
            assert pg.stats.retries == 0, "the lock spares every retry"


# The role split: the tables belong to a role that cannot log in, and the engine's role reads
# and writes their rows but cannot alter, drop or truncate them. `lockdown` refuses a superuser
# and can run again; the engine starts on the tables it made.
def test_roles_keep_the_engine_to_rows() -> None:
    db = setup("contract_roles")
    owner = db.one("SELECT tableowner FROM pg_tables WHERE tablename = 'cells'")
    assert owner == OWNER
    with connect(db.url) as engine:
        for statement in [
            "DROP TABLE cells",
            "TRUNCATE cells",
            "ALTER TABLE cells ADD COLUMN x BIGINT",
            "DROP TABLE leangage_idempotency",
            "DROP TABLE leangage_version",
            "TRUNCATE leangage_version",
        ]:
            with pytest.raises(psycopg.errors.InsufficientPrivilege):
                engine.execute(statement)
    pg = db.engine(1, Config())
    assert run(pg, 1, Add(0, 1)) == 1
    lockdown(CELLS, db.admin_url(), OWNER, ENGINE_ROLE)
    with pytest.raises(Broken):
        lockdown(CELLS, db.admin_url(), OWNER, "postgres")
    with pytest.raises(Broken):
        lockdown(CELLS, db.admin_url(), ENGINE_ROLE, OWNER)
    assert db.cell(1, 0) == 1


# Item 8: an engine reads the rows another engine wrote, whichever path it takes, and reads no row
# while the version is the one it remembers.
def test_other_engines_writes_are_read() -> None:
    db = setup("contract_other")
    a = db.engine(2, Config())
    b = db.engine(2, Config())
    assert run(a, 1, Add(0, 5)) == 5
    assert a.stats.loads == 1
    assert run(a, 1, Get(0)) == 5
    assert run(a, 1, Add(0, 1)) == 6
    assert a.stats.loads == 1, "the remembered snapshot, on both paths"
    assert run(b, 1, Add(0, 10)) == 16
    assert run(a, 1, Get(0)) == 16, "the read-only path"
    assert a.stats.loads == 2
    assert run(b, 1, Move(0, 1, 6)) == 10
    assert run(a, 1, Add(1, 1)) == 7, "the write path"
    assert run_keyed(b, 1, "k", Get(0)) == 10, "keyed"
    assert run(b, 1, Get(1)) == 7
    assert a.stats.loads == 3
    assert b.stats.loads == 2, "its own commit remembered"
    assert db.cells(1) == {0: 10, 1: 7}


ADVANCE = (
    "INSERT INTO leangage_version (tenant_id, version) VALUES ($1, 1) "
    "ON CONFLICT (tenant_id) DO UPDATE SET version = leangage_version.version + 1 "
    "RETURNING version"
)


# Item 8, on PostgreSQL's side: two transactions that read a tenant's version and advance it
# cannot both commit, whether the row exists or not. The second fails with 40001, which the
# engines retry, and not with 23505.
def test_version_rows_conflict() -> None:
    db = setup("contract_version")
    pg = db.engine(1, Config())
    run(pg, 2, Add(0, 1))
    for tenant, before in [(1, 0), (2, 1)]:
        with connect(db.url) as first, connect(db.url) as second:
            for c in (first, second):
                c.execute("BEGIN ISOLATION LEVEL SERIALIZABLE")
                row = c.execute(
                    "SELECT version FROM leangage_version WHERE tenant_id = $1",
                    [tenant],
                ).fetchone()
                assert (0 if row is None else row[0]) == before
            advanced = first.execute(ADVANCE, [tenant]).fetchone()
            assert advanced is not None and advanced[0] == before + 1
            with ThreadPoolExecutor(1) as pool:
                waiting = pool.submit(second.execute, ADVANCE, [tenant])
                time.sleep(0.2)
                assert not waiting.done(), f"tenant {tenant}: waits for the first"
                first.execute("COMMIT")
                error = waiting.exception(T)
            assert isinstance(error, psycopg.Error), f"tenant {tenant}: {error}"
            assert error.sqlstate == "40001", f"tenant {tenant}: {error}"
            second.execute("ROLLBACK")


# Item 8: a COMMIT of unknown outcome forgets the tenant's snapshot. The engine reads the rows
# again, whether the COMMIT ran or not, and after another engine's commit. The first ten commands
# go to another tenant, as in `test_lost_commit_without_key_is_unknown`.
def test_lost_commit_forgets_the_snapshot() -> None:
    db = setup("contract_forget")
    proxy = Proxy(cluster())
    pg = db.engine_at(proxy.url(db.name), 1, config(20, True, None))
    other = db.engine(1, Config())
    for i in range(10):
        assert run(pg, 3, Add(0, 1)) == i + 1
    assert run(pg, 1, Add(0, 5)) == 5
    loads = pg.stats.loads
    proxy.arm(Fault.DROP_BEFORE)
    assert outcome(run, pg, 1, Add(0, 1)) is CommitUnknown
    assert run(pg, 1, Get(0)) == 5, "not committed"
    assert run(other, 1, Add(0, 10)) == 15
    assert run(pg, 1, Get(0)) == 15, "the other engine's commit"
    proxy.arm(Fault.DROP_AFTER)
    assert outcome(run, pg, 1, Add(0, 1)) is CommitUnknown
    assert run(pg, 1, Add(0, 1)) == 17, "committed"
    assert run(other, 1, Get(0)) == 17
    assert pg.stats.loads - loads == 3, (
        "every attempt after a lost COMMIT reads the rows"
    )
    assert proxy.outcomes() == [Outcome.NOT_SENT, Outcome.COMMITTED]


# Item 8: a refusal, and an attempt rolled back by a terminated backend, leave the remembered
# snapshot as the last commit left it: the refusal reads no row, and the retry runs the command
# on what was committed.
def test_refusals_and_rollbacks_keep_the_snapshot() -> None:
    db = setup("contract_keep")
    armed = threading.Event()

    def kill_armed(a: Attempt) -> None:
        if armed.is_set():
            armed.clear()
            kill(db, a.pid)

    hook, _ = hook_at(Point.WRITTEN, float("inf"), kill_armed)
    pg = db.engine(2, config(20, True, hook))
    assert run(pg, 1, Add(0, 5)) == 5
    assert outcome(run, pg, 1, Add(0, -6)) == ("refused", NEGATIVE)
    assert outcome(run_keyed, pg, 1, "k", Add(0, -6)) == ("refused", NEGATIVE)
    assert run(pg, 1, Get(0)) == 5
    assert run(pg, 1, Add(0, 1)) == 6
    assert pg.stats.loads == 1, "one read of the rows"
    fresh = db.engine(2, Config())
    assert outcome(run, fresh, 1, Add(0, -7)) == ("refused", NEGATIVE)
    assert run(fresh, 1, Get(0)) == 6
    assert fresh.stats.loads == 1, "the snapshot loaded for a refusal"
    before = pg.stats.loads
    assert run(pg, 2, Add(0, 3)) == 3
    armed.set()
    assert outcome(run, pg, 2, Add(0, 4)) is CommitUnknown
    assert run(pg, 2, Add(0, 4)) == 7, "on the committed rows"
    assert db.cell(2, 0) == 7
    assert run(pg, 3, Add(0, 3)) == 3
    armed.set()
    assert run_keyed(pg, 3, "k", Add(0, 4)) == 7, "retried"
    assert db.cell(3, 0) == 7
    assert pg.stats.loads - before == 4


# Item 8: the engine remembers at most `cache_tenants` tenants and forgets the one it used least
# recently; with 0 it remembers none.
def test_remembers_at_most_cache_tenants() -> None:
    db = setup("contract_capacity")
    pg = db.engine(1, Config(cache_tenants=2))
    for tenant in (1, 2, 3):
        run(pg, tenant, Add(0, 1))
    assert pg.cached() == 2
    assert pg.stats.loads == 3
    assert run(pg, 2, Get(0)) == 1
    assert pg.stats.loads == 3, "tenant 2 remembered"
    assert run(pg, 1, Get(0)) == 1
    assert pg.stats.loads == 4, "tenant 1 forgotten"
    assert run(pg, 2, Get(0)) == 1
    assert run(pg, 1, Get(0)) == 1
    assert pg.stats.loads == 4, "tenants 1 and 2 remembered"
    assert run(pg, 3, Get(0)) == 1
    assert pg.stats.loads == 5, "tenant 3 forgotten"
    assert pg.cached() == 2
    pg = db.engine(1, Config(cache_tenants=0))
    for _ in range(3):
        run(pg, 1, Add(0, 1))
        run(pg, 1, Get(0))
    assert pg.cached() == 0
    assert pg.stats.loads == 6


def mover_reading(pg: PgEngine, tenant: int, c: int) -> list[tuple[int, int]]:
    """Eight moves of one unit around the four cells, each followed by a read of its source; the
    accepted moves."""
    moved = []
    for i in range(8):
        src, dst = (c + i) % 4, (c + i + 1) % 4
        try:
            pg.execute(actor(tenant), Move(src, dst, 1))
            moved.append((src, dst))
        except Refused:
            pass
        pg.execute(actor(tenant), Get(src))
    return moved


# Item 8 with SERIALIZABLE: two engines, each with 32 threads, move units between four cells of
# one tenant, with and without the advisory lock. Every cell holds what the accepted moves left,
# and both engines then read it.
def test_concurrent_engines_are_serial() -> None:
    db = setup("contract_engines")
    for tenant, lock in [(1, True), (2, False)]:
        engines = [db.engine(4, config(1000, lock, None)) for _ in range(2)]
        for cell in range(4):
            run(engines[0], tenant, Add(cell, 100))
        with ThreadPoolExecutor(64) as pool:
            futures = [
                pool.submit(mover_reading, engines[c % 2], tenant, c) for c in range(64)
            ]
            results = [f.result() for f in futures]
        expected = {0: 100, 1: 100, 2: 100, 3: 100}
        accepted = 0
        for moved in results:
            for src, dst in moved:
                expected[src] -= 1
                expected[dst] += 1
                accepted += 1
        assert accepted == 512, f"lock {lock}"
        assert db.cells(tenant) == expected, f"lock {lock}"
        for pg in engines:
            for cell, v in expected.items():
                assert run(pg, tenant, Get(cell)) == v, f"lock {lock}"
