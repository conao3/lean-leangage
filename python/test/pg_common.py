"""A small kernel written in Python for the engine's tests, a proxy that loses a COMMIT, and the
queries a test makes as the server's superuser."""

import select
import socket
import threading
import time
from collections import deque
from collections.abc import Callable
from dataclasses import dataclass
from enum import Enum
from typing import Any

import psycopg
from leanharbor import Kernel, Refused, Storage, sql
from leanharbor.pg import Attempt, Config, PgEngine, Point
from leanharbor.pg.testing import ENGINE_ROLE, Cluster, cluster, connect


@dataclass(frozen=True)
class Actor:
    tenant: int
    user: int


@dataclass(frozen=True)
class Add:
    cell: int
    delta: int


@dataclass(frozen=True)
class Move:
    src: int
    dst: int
    amount: int


@dataclass(frozen=True)
class Get:
    cell: int


@dataclass(frozen=True)
class Poke:
    """Claims to read only, and writes."""

    cell: int


NEGATIVE = "negative"


def transition(
    _: Actor, snap: dict[int, int], cmd: Any
) -> tuple[list[tuple[int, int]], int]:
    """Numbered cells of integers per tenant."""

    def get(c: int) -> int:
        return snap.get(c, 0)

    match cmd:
        case Add(cell, delta):
            v = get(cell) + delta
            if v < 0:
                raise Refused(NEGATIVE)
            return [(cell, v)], v
        case Move(src, dst, amount):
            f = get(src) - amount
            if f < 0:
                raise Refused(NEGATIVE)
            return [(src, f), (dst, get(dst) + amount)], f
        case Get(cell):
            return [], get(cell)
        case Poke(cell):
            return [(cell, get(cell) + 1)], get(cell) + 1
    raise ValueError(cmd)


CELLS_KERNEL = Kernel(
    init=dict,
    tenant=lambda actor: actor.tenant,
    transition=transition,
    apply=lambda snap, ws: {**snap, **dict(ws)},
    read_only=lambda cmd: isinstance(cmd, (Get, Poke)),
)


def _load(rows: list[list[list[sql.Val]]]) -> dict[int, int] | None:
    if len(rows) != 1:
        return None
    snap = {}
    for row in rows[0]:
        match row:
            case [sql.Val_int(v=id), sql.Val_int(v=v)]:
                snap[id] = v
            case _:
                return None
    return snap


def _decode(stored: bytes) -> int | None:
    if len(stored) != 8:
        return None
    return int.from_bytes(stored, "big", signed=True)


CELLS = Storage(
    kernel=CELLS_KERNEL,
    tables=lambda: [
        sql.Tab(
            name="cells",
            cols=[
                sql.Col(name="id", kind=sql.Kind.int, nullable=False),
                sql.Col(name="v", kind=sql.Kind.int, nullable=False),
            ],
            kl=1,
        )
    ],
    load=_load,
    writes=lambda ws: [
        sql.Write_put(table=0, keyLen=1, row=[sql.Val_int(v=id), sql.Val_int(v=v)])
        for id, v in ws
    ],
    encode_reply=lambda reply: reply.to_bytes(8, "big", signed=True),
    decode_reply=_decode,
)


def actor(tenant: int) -> Actor:
    return Actor(tenant, 1)


class Db:
    """One database of the test process's server, with the tables of `CELLS` made by
    `lockdown`. `url` is the engine role's connection string."""

    def __init__(self, name: str) -> None:
        self.name = name
        self.url = cluster().locked(CELLS, name)
        self.admin = connect(cluster().admin_url(name))
        self._lock = threading.Lock()

    def engine(self, size: int, config: Config | None = None) -> PgEngine:
        return self.engine_at(self.url, size, config)

    def engine_at(self, url: str, size: int, config: Config | None = None) -> PgEngine:
        return PgEngine.connect(CELLS, url, size, config)

    def admin_url(self) -> str:
        return cluster().admin_url(self.name)

    def one(self, query: str, params: list[Any] | None = None) -> Any:
        """The first column of the first row, on the superuser's connection."""
        with self._lock:
            row = self.admin.execute(query, params).fetchone()
        assert row is not None
        return row[0]

    def cells(self, tenant: int) -> dict[int, int]:
        with self._lock:
            rows = self.admin.execute(
                "SELECT id, v FROM cells WHERE tenant_id = $1", [tenant]
            ).fetchall()
        return dict(rows)

    def cell(self, tenant: int, id: int) -> int | None:
        return self.cells(tenant).get(id)

    def replies(self, tenant: int) -> int:
        return self.one(
            "SELECT count(*) FROM leanharbor_idempotency WHERE tenant_id = $1", [tenant]
        )

    def advisory_locks(self) -> int:
        """Advisory locks in this database held or awaited by any session but this one."""
        return self.one(
            "SELECT count(*) FROM pg_locks WHERE locktype = 'advisory' "
            "AND pid <> pg_backend_pid() "
            "AND database = (SELECT oid FROM pg_database WHERE datname = current_database())"
        )

    def no_advisory_locks(self, within: float) -> int:
        """Waits until no session but this one holds an advisory lock; the number left."""
        deadline = time.monotonic() + within
        while True:
            n = self.advisory_locks()
            if n == 0 or time.monotonic() > deadline:
                return n
            time.sleep(0.01)


def setup(name: str) -> Db:
    return Db(name)


def kill(db: Db, pid: int) -> None:
    """Terminates the backend and waits until it is gone."""
    assert db.one("SELECT pg_terminate_backend($1)", [pid]), f"backend {pid}"
    for _ in range(500):
        if db.one("SELECT count(*) FROM pg_stat_activity WHERE pid = $1", [pid]) == 0:
            return
        time.sleep(0.01)
    raise AssertionError(f"backend {pid} still runs")


class Recorder:
    """Every attempt a hook saw."""

    def __init__(self) -> None:
        self.seen: list[Attempt] = []
        self.fired = 0
        self.lock = threading.Lock()

    def at(self, point: Point) -> list[Attempt]:
        with self.lock:
            return [a for a in self.seen if a.point == point]


def hook_at(
    point: Point, times: float, f: Callable[[Attempt], None]
) -> tuple[Callable[[Attempt], None], Recorder]:
    """A hook that runs `f` at `point` for the first `times` attempts that reach it, and records
    every attempt it sees."""
    recorder = Recorder()

    def hook(attempt: Attempt) -> None:
        with recorder.lock:
            recorder.seen.append(attempt)
            run = attempt.point == point and recorder.fired < times
            if attempt.point == point:
                recorder.fired += 1
        if run:
            f(attempt)

    return hook, recorder


def config(
    max_attempts: int, tenant_lock: bool, hook: Callable[[Attempt], None] | None
) -> Config:
    return Config(max_attempts=max_attempts, tenant_lock=tenant_lock, hook=hook)


class Fault(Enum):
    """What the proxy does with the next COMMIT it relays. `DROP_BEFORE` closes both sides
    without sending COMMIT: the server rolls back. `DROP_AFTER` sends COMMIT, waits for the
    server's answer, then closes both sides without relaying it."""

    DROP_BEFORE = "drop before"
    DROP_AFTER = "drop after"


class Outcome(Enum):
    """What the server answered a COMMIT the proxy kept from the client."""

    NOT_SENT = "not sent"
    COMMITTED = "committed"
    FAILED = "failed"


def _next_message(buf: bytearray, typed: bool) -> bytes | None:
    """The next whole message in `buf`: the untyped startup message first, then messages of a
    type byte, a length and a body."""
    head, len_at = (5, 1) if typed else (4, 0)
    if len(buf) < head:
        return None
    total = int.from_bytes(buf[len_at : len_at + 4], "big") + len_at
    if len(buf) < total:
        return None
    message = bytes(buf[:total])
    del buf[:total]
    return message


class Proxy:
    """A TCP proxy in front of the server's Unix socket that can lose the next COMMIT. It reads
    the frontend protocol (the startup message, then typed messages) and acts on a simple-query
    `COMMIT`, which is how the engine commits. Its connection string turns off the requests for
    TLS and GSSAPI encryption, so the startup message comes first."""

    def __init__(self, cluster: Cluster) -> None:
        self._socket = str(cluster.socket())
        self._listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self._listener.bind(("127.0.0.1", 0))
        self._listener.listen(64)
        self.port = self._listener.getsockname()[1]
        self._faults: deque[Fault] = deque()
        self._outcomes: list[Outcome] = []
        self._lock = threading.Lock()
        threading.Thread(target=self._accept, daemon=True).start()

    def arm(self, fault: Fault) -> None:
        with self._lock:
            self._faults.append(fault)

    def outcomes(self) -> list[Outcome]:
        with self._lock:
            return list(self._outcomes)

    def url(self, database: str) -> str:
        """The engine role's connection string to `database` through the proxy."""
        return (
            f"host=127.0.0.1 port={self.port} user={ENGINE_ROLE} dbname={database} "
            "sslmode=disable gssencmode=disable"
        )

    def _accept(self) -> None:
        while True:
            client, _ = self._listener.accept()
            server = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            try:
                server.connect(self._socket)
            except OSError:
                client.close()
                continue
            threading.Thread(
                target=self._relay, args=(client, server), daemon=True
            ).start()

    def _record(self, outcome: Outcome) -> None:
        with self._lock:
            self._outcomes.append(outcome)

    def _relay(self, client: socket.socket, server: socket.socket) -> None:
        client.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        from_client, from_server = bytearray(), bytearray()
        started = swallowing = committed = False
        try:
            while True:
                ready, _, _ = select.select([client, server], [], [])
                if client in ready:
                    data = client.recv(16384)
                    if not data:
                        return
                    from_client += data
                    while (m := _next_message(from_client, started)) is not None:
                        started = True
                        if m[0] == ord("Q") and m[5:] == b"COMMIT\0":
                            with self._lock:
                                fault = self._faults.popleft() if self._faults else None
                            if fault is Fault.DROP_BEFORE:
                                self._record(Outcome.NOT_SENT)
                                return
                            if fault is Fault.DROP_AFTER:
                                swallowing = True
                        server.sendall(m)
                if server in ready:
                    data = server.recv(16384)
                    if not data:
                        return
                    if not swallowing:
                        client.sendall(data)
                        continue
                    from_server += data
                    while (m := _next_message(from_server, True)) is not None:
                        # COMMIT ends with ReadyForQuery `I`: outside a transaction.
                        if m[0] == ord("C") and m[5:].startswith(b"COMMIT"):
                            committed = True
                        if m[0] == ord("Z") and m[5:6] == b"I":
                            outcome = Outcome.COMMITTED if committed else Outcome.FAILED
                            self._record(outcome)
                            return
        except OSError:
            return
        finally:
            client.close()
            server.close()


def admin_connection(db: Db) -> psycopg.Connection[Any]:
    """Another superuser's connection to the test's database."""
    return connect(db.admin_url())
