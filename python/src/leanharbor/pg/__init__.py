"""An engine that stores each tenant's snapshot in PostgreSQL, as `Leanharbor.Storage.Stored`
describes. It is trusted: no theorem covers this file.

At start it creates the kernel's tables with the statements of the generated `create` and
`render`. Each command runs in one `SERIALIZABLE` transaction: it reads the tenant's version, takes
the snapshot it remembers for that version or else reads the tenant's rows with the generated
`select` of every table and builds the snapshot with the storage's `load`, calls `transition`, and
sends the statements the generated `compile` makes of the generated `plan` of each write. The only
other statements are the constant ones of this file: the transaction control, the advisory locks,
and the framework's tables `leanharbor_idempotency` and `leanharbor_version`, of the same form as
the Rust engine's, so that the Rust and the Python engine can share a database.

The contract (the engine's side of `Storage.Stored`):

1. One attempt reads one tenant, calls `transition`, writes and commits in one `SERIALIZABLE`
   transaction.
2. A retry opens a new transaction, reads the rows again and calls `transition` again. An attempt
   is retried after a lost connection, SQLSTATE 40001, 40P01, 57P01, 57P02 or 53200 from a full
   table of serializable conflicts, and, with an idempotency key, 23505 and a lost COMMIT; at most
   `Config.max_attempts` attempts, 20 by default.
3. A refused command rolls back and writes no row.
4. The app's writes and the reply stored under an idempotency key commit in one transaction.
5. The tenant's advisory lock is taken before `BEGIN` and released before the connection returns
   to the pool; a connection that fails to release it is closed.
6. A command `read_only` accepts runs in a `SERIALIZABLE READ ONLY DEFERRABLE` transaction,
   without the advisory lock and without an idempotency key (a keyed request takes the write
   path), and fails if its write set stores a row.
7. A request without an idempotency key whose connection is lost during COMMIT, or whose COMMIT
   fails with 57P01 or 57P02, fails with `CommitUnknown`.
8. A transaction whose write set stores a row advances the tenant's row of `leanharbor_version` by
   one (from 0 when it has none). An attempt reads that row first and runs the command on the
   snapshot the engine remembers for the tenant at that version, or, when it remembers none, on
   the snapshot `load` builds of the rows it reads. After a commit the engine remembers the
   snapshot `apply` computed, at the version the transaction left; after a refusal, and on the
   read-only path, the snapshot the command ran on; after any other end of the attempt, a COMMIT
   of unknown outcome included, nothing for the tenant. It remembers at most
   `Config.cache_tenants` tenants and forgets the one it used least recently.

Every request runs on its caller's thread to its end, so a caller whose client stops waiting (a
closed HTTP connection) does not interrupt an attempt between its lock and its unlock.

Each value goes to PostgreSQL as a parameter of the type of its kind (`BIGINT`, `BOOLEAN`, `TEXT`,
`BYTEA`; `NULL` untyped), so a value of another kind than its column's fails the statement; a
column is read back by its type's OID.
"""

import random
import re
import threading
import time
from collections import OrderedDict
from collections.abc import Callable
from dataclasses import dataclass
from enum import Enum
from typing import Any

import psycopg
from psycopg.adapt import AdaptersMap
from psycopg.pq import TransactionStatus
from psycopg.types.numeric import Int8Dumper
from psycopg.types.string import StrDumper

from leanharbor import sql
from leanharbor.engine import (
    Broken,
    CommitUnknown,
    DatabaseError,
    EngineError,
    IdempotencyConflict,
    Refused,
    RetriesExhausted,
    Storage,
)

__all__ = [
    "Attempt",
    "Config",
    "PgEngine",
    "Point",
    "Stats",
    "TxInfo",
    "lockdown",
]

# The replies of the commands run under an idempotency key, per tenant, scope and key.
FRAMEWORK_DDL = (
    "CREATE TABLE IF NOT EXISTS leanharbor_idempotency ("
    "tenant_id BIGINT NOT NULL, scope TEXT NOT NULL, key TEXT NOT NULL, "
    "fingerprint BYTEA NOT NULL, reply BYTEA NOT NULL, PRIMARY KEY (tenant_id, scope, key))"
)
# Each tenant's version: a transaction that writes the tenant's rows advances it by one.
VERSION_DDL = (
    "CREATE TABLE IF NOT EXISTS leanharbor_version ("
    "tenant_id BIGINT PRIMARY KEY, version BIGINT NOT NULL)"
)
FRAMEWORK_TABLES = ["leanharbor_idempotency", "leanharbor_version"]
# The tenant's version; no row is version 0.
VERSION = "SELECT version FROM leanharbor_version WHERE tenant_id = $1"
ADVANCE = (
    "INSERT INTO leanharbor_version (tenant_id, version) VALUES ($1, 1) "
    "ON CONFLICT (tenant_id) DO UPDATE SET version = leanharbor_version.version + 1 "
    "RETURNING version"
)
STORED_REPLY = (
    "SELECT fingerprint, reply FROM leanharbor_idempotency "
    "WHERE tenant_id = $1 AND scope = $2 AND key = $3"
)
STORE_REPLY = (
    "INSERT INTO leanharbor_idempotency "
    "(tenant_id, scope, key, fingerprint, reply) VALUES ($1, $2, $3, $4, $5)"
)
# Held while the tables are created, so that engines starting together do not race in
# `CREATE TABLE`. The two-key form, whose keys never meet a tenant's lock.
SCHEMA_LOCK = "SELECT pg_advisory_lock(1819173234, 0)"
SCHEMA_UNLOCK = "SELECT pg_advisory_unlock(1819173234, 0)"
# The tenant's lock: the tenant id as a `BIGINT`.
TENANT_LOCK = "SELECT pg_advisory_lock($1)"
UNLOCK_ALL = "SELECT pg_advisory_unlock_all()"
BACKEND_PID = "SELECT pg_backend_pid()"
TX_INFO = (
    "SELECT pg_backend_pid(), current_setting('transaction_isolation'), "
    "current_setting('transaction_read_only'), current_setting('transaction_deferrable'), "
    "(SELECT virtualxid FROM pg_locks WHERE locktype = 'virtualxid' AND pid = pg_backend_pid())"
)
BEGIN_WRITE = "BEGIN ISOLATION LEVEL SERIALIZABLE"
BEGIN_READ = "BEGIN ISOLATION LEVEL SERIALIZABLE, READ ONLY, DEFERRABLE"
COMMIT = "COMMIT"
ROLLBACK = "ROLLBACK"

_RETRIED = {"40001", "40P01", "57P01", "57P02"}
_UNIQUE_VIOLATION = "23505"
_OUT_OF_MEMORY = "53200"
_SHUTDOWN = {"57P01", "57P02"}

_INT8, _BOOL, _TEXT, _BYTEA = 20, 16, 25, 17

_ADAPTERS = AdaptersMap(psycopg.adapters)
_ADAPTERS.register_dumper(int, Int8Dumper)
_ADAPTERS.register_dumper(str, StrDumper)


class Point(Enum):
    """A point of an attempt where `Config.hook` is called."""

    # Before `BEGIN`, holding the tenant's advisory lock if `Config.tenant_lock`. Not on the
    # read-only path.
    LOCKED = "locked"
    # The version is read, and the rows unless the engine remembers the snapshot of that version;
    # `transition` has not run.
    LOADED = "loaded"
    # The writes and the stored reply are sent, `COMMIT` is not. Not on the read-only path.
    WRITTEN = "written"


@dataclass(frozen=True)
class TxInfo:
    """The transaction of an attempt, as PostgreSQL reports it."""

    vxid: str
    isolation: str
    read_only: bool
    deferrable: bool


@dataclass(frozen=True)
class Attempt:
    """Where an attempt is when `Config.hook` is called. `pid` is the process of the attempt's
    connection; `tx` is set from `Point.LOADED` on."""

    point: Point
    tenant: int
    pid: int
    tx: TxInfo | None


@dataclass(frozen=True)
class Config:
    """`max_attempts`: attempts of one command before `RetriesExhausted`. `tenant_lock`: take the
    tenant's advisory lock before each write attempt; it spares retries, and `SERIALIZABLE` keeps
    the commits serial without it. `hook`: called at each `Point` of each attempt, which waits for
    it to return; for tests that inject faults. `cache_tenants`: tenants whose snapshot the engine
    remembers at once; 0 remembers none."""

    max_attempts: int = 20
    tenant_lock: bool = True
    hook: Callable[[Attempt], None] | None = None
    cache_tenants: int = 1024


class Stats:
    """What the engine did, counted since it started. `commits` counts the accepted commands
    committed on both paths, `replays` the requests answered with a stored reply, `reads` the
    attempts on the read-only path, also counted in `attempts`, and `loads` the attempts that read
    the tenant's rows: the engine remembered no snapshot at the version they read."""

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self.attempts = 0
        self.retries = 0
        self.commits = 0
        self.replays = 0
        self.reads = 0
        self.loads = 0

    def bump(self, name: str) -> None:
        with self._lock:
            setattr(self, name, getattr(self, name) + 1)

    def counts(self) -> tuple[int, int, int, int, int, int]:
        """`(attempts, retries, commits, replays, reads, loads)`."""
        with self._lock:
            return (
                self.attempts,
                self.retries,
                self.commits,
                self.replays,
                self.reads,
                self.loads,
            )


class _Failure(Exception):
    """Why an attempt ended without a decision to return."""

    def retryable(self, keyed: bool) -> bool:
        raise NotImplementedError

    def error(self) -> EngineError:
        raise NotImplementedError


class _Postgres(_Failure):
    """The attempt did not commit. `lost`: the connection is gone."""

    def __init__(self, cause: psycopg.Error, lost: bool) -> None:
        super().__init__(cause)
        self.cause = cause
        self.lost = lost

    def retryable(self, keyed: bool) -> bool:
        state = self.cause.sqlstate
        return (
            self.lost
            or _ssi_exhausted(self.cause)
            or state in _RETRIED
            or (keyed and state == _UNIQUE_VIOLATION)
        )

    def error(self) -> EngineError:
        return DatabaseError(str(self.cause))


class _Pool(_Failure):
    """No connection: the attempt did not start."""

    def retryable(self, keyed: bool) -> bool:
        return True

    def error(self) -> EngineError:
        return DatabaseError(str(self))


class _CommitLost(_Failure):
    """The connection was lost during COMMIT."""

    def retryable(self, keyed: bool) -> bool:
        return keyed

    def error(self) -> EngineError:
        return CommitUnknown()


class _Final(_Failure):
    """Retrying cannot help."""

    def __init__(self, error: EngineError) -> None:
        super().__init__(error)
        self.final = error

    def retryable(self, keyed: bool) -> bool:
        return False

    def error(self) -> EngineError:
        return self.final


def _ssi_exhausted(e: psycopg.Error) -> bool:
    """SERIALIZABLE ran out of its shared memory for conflicts; PostgreSQL aborted the
    transaction."""
    if e.sqlstate != _OUT_OF_MEMORY or e.diag is None:
        return False
    return "RWConflictPool" in (e.diag.message_primary or "") or (
        "max_pred_locks_per_transaction" in (e.diag.message_hint or "")
    )


def _broken(message: str) -> _Final:
    return _Final(Broken(message))


@dataclass(frozen=True)
class _Idempotency:
    scope: str
    key: str
    fingerprint: bytes


@dataclass(frozen=True)
class _Refusal:
    refused: Refused


class _Cache:
    """The snapshots the engine remembers, each with the tenant's version it stands for, at most
    `capacity` tenants. A snapshot taken out is held by one thread until it is put back."""

    def __init__(self, capacity: int) -> None:
        self._capacity = capacity
        self._lock = threading.Lock()
        self._tenants: OrderedDict[int, tuple[int, Any]] = OrderedDict()

    def take(self, tenant: int, version: int) -> Any | None:
        """The snapshot of the tenant at `version`, which the cache no longer holds. A snapshot
        of an earlier version is forgotten."""
        with self._lock:
            found = self._tenants.get(tenant)
            if found is None or found[0] > version:
                return None
            del self._tenants[tenant]
            return found[1] if found[0] == version else None

    def put(self, tenant: int, version: int, snap: Any) -> None:
        """Remembers the snapshot of the tenant at `version`, unless it holds one of a later
        version, and forgets the tenant used least recently beyond the capacity."""
        if self._capacity == 0:
            return
        with self._lock:
            found = self._tenants.get(tenant)
            if found is not None and found[0] > version:
                return
            self._tenants[tenant] = (version, snap)
            self._tenants.move_to_end(tenant)
            while len(self._tenants) > self._capacity:
                self._tenants.popitem(last=False)

    def __len__(self) -> int:
        with self._lock:
            return len(self._tenants)


def _param(v: sql.Val) -> Any:
    """A value as the parameter of the type of its kind."""
    match v:
        case sql.Val_int(v=n):
            return n
        case sql.Val_bool(v=b):
            return b
        case sql.Val_text(v=t):
            return t
        case sql.Val_bytes(v=bs):
            return bytes(bs)
        case sql.Val_null():
            return None
    raise _broken(f"{v!r} is not a value")


def _params(ps: list[sql.Val]) -> list[Any]:
    return [_param(p) for p in ps]


def _values(cursor: psycopg.Cursor[Any], row: tuple[Any, ...]) -> list[sql.Val]:
    """A row as values, by the type of each column."""
    vals: list[sql.Val] = []
    for column, x in zip(cursor.description or [], row, strict=True):
        oid = column.type_code
        if oid not in (_INT8, _BOOL, _TEXT, _BYTEA):
            raise _broken(f"a column of type {oid}")
        if x is None:
            vals.append(sql.Val_null())
        elif oid == _INT8:
            vals.append(sql.Val_int(v=x))
        elif oid == _BOOL:
            vals.append(sql.Val_bool(v=x))
        elif oid == _TEXT:
            vals.append(sql.Val_text(v=x))
        else:
            vals.append(sql.Val_bytes(v=list(x)))
    return vals


def _signed(tenant: int) -> int:
    """The tenant id as the `Int64` with the same bits."""
    return tenant - (1 << 64) if tenant >= 1 << 63 else tenant


def _backoff(attempt: int) -> float:
    cap_us = 1000 << min(attempt, 8)
    return (random.randrange(cap_us) + 100) / 1_000_000


def _connect(url: str) -> psycopg.Connection[Any]:
    """A connection that runs each statement on its own unless a `BEGIN` opened a transaction,
    and sends the text of a statement as it is, with `$1`, `$2`, ... for the parameters."""
    return psycopg.connect(
        url, autocommit=True, cursor_factory=psycopg.RawCursor, context=_ADAPTERS
    )


def _run(
    conn: psycopg.Connection[Any], text: str, params: list[Any] | None = None
) -> psycopg.Cursor[Any]:
    """Runs one statement; a constant without parameters is sent as a simple query."""
    try:
        if params is None:
            return conn.execute(text, prepare=False)
        return conn.execute(text, params)
    except psycopg.Error as e:
        raise _Postgres(e, conn.closed) from e


def _commit(conn: psycopg.Connection[Any]) -> None:
    """A COMMIT that failed without a server's error code, or because the server ended the
    connection, may have committed."""
    try:
        conn.execute(COMMIT, prepare=False)
    except psycopg.Error as e:
        if e.sqlstate is None or e.sqlstate in _SHUTDOWN:
            raise _CommitLost() from e
        raise _Postgres(e, conn.closed) from e


class _Connections:
    """A pool of up to `size` connections, opened when they are first needed."""

    def __init__(self, url: str, size: int) -> None:
        self._url = url
        self._slots = threading.BoundedSemaphore(size)
        self._idle: list[psycopg.Connection[Any]] = []
        self._lock = threading.Lock()

    def get(self) -> psycopg.Connection[Any]:
        self._slots.acquire()
        with self._lock:
            conn = self._idle.pop() if self._idle else None
        if conn is not None:
            return conn
        try:
            return _connect(self._url)
        except psycopg.Error as e:
            self._slots.release()
            raise _Pool(str(e)) from e

    def put(self, conn: psycopg.Connection[Any], keep: bool) -> None:
        """Keeps an open connection outside a transaction, and closes any other."""
        if (
            keep
            and not conn.closed
            and conn.info.transaction_status == TransactionStatus.IDLE
        ):
            with self._lock:
                self._idle.append(conn)
        else:
            conn.close()
        self._slots.release()

    def idle(self) -> int:
        with self._lock:
            return len(self._idle)

    def close(self) -> None:
        with self._lock:
            idle, self._idle = self._idle, []
        for conn in idle:
            conn.close()


def _create(conn: psycopg.Connection[Any], tables: list[sql.Tab]) -> None:
    conn.execute(SCHEMA_LOCK, prepare=False)
    try:
        conn.execute(FRAMEWORK_DDL, prepare=False)
        conn.execute(VERSION_DDL, prepare=False)
        for t in tables:
            conn.execute(sql.render(sql.create(t)), prepare=False)
    finally:
        conn.execute(SCHEMA_UNLOCK, prepare=False)


class PgEngine:
    """The engine: a pool of connections to one database, and the snapshots it remembers.
    `connect` opens it."""

    def __init__(
        self,
        storage: Storage,
        tables: list[sql.Tab],
        pool: _Connections,
        config: Config,
    ) -> None:
        self._storage = storage
        self._kernel = storage.kernel
        self._tables = tables
        self._pool = pool
        self._config = config
        self._cache = _Cache(config.cache_tenants)
        self.stats = Stats()

    @classmethod
    def connect(
        cls, storage: Storage, url: str, size: int, config: Config | None = None
    ) -> "PgEngine":
        """Opens a pool of up to `size` connections to `url` and creates the tables that do not
        exist, with the generated `create` of each of `storage.tables()` and the framework's
        tables."""
        tables = storage.tables()
        if not sql.valid(tables):
            raise Broken("the tables are not valid")
        try:
            with _connect(url) as conn:
                _create(conn, tables)
        except psycopg.Error as e:
            raise DatabaseError(str(e)) from e
        return cls(storage, tables, _Connections(url, size), config or Config())

    def idle(self) -> int:
        """Connections open and idle in the pool."""
        return self._pool.idle()

    def cached(self) -> int:
        """Tenants whose snapshot the engine remembers."""
        return len(self._cache)

    def close(self) -> None:
        """Closes the idle connections."""
        self._pool.close()

    def execute(self, actor: Any, cmd: Any) -> Any:
        return self._execute(actor, cmd, None)

    def execute_idempotent(
        self, actor: Any, scope: str, key: str, fingerprint: bytes, cmd: Any
    ) -> Any:
        return self._execute(actor, cmd, _Idempotency(scope, key, fingerprint))

    def _execute(self, actor: Any, cmd: Any, idem: _Idempotency | None) -> Any:
        try:
            result = self._attempts(actor, cmd, idem)
        except (Refused, EngineError):
            raise
        except Exception as e:
            raise Broken(f"the request failed: {e!r}") from e
        if isinstance(result, _Refusal):
            raise result.refused
        return result

    def _attempts(self, actor: Any, cmd: Any, idem: _Idempotency | None) -> Any:
        read = idem is None and self._kernel.read_only(cmd)
        keyed = idem is not None
        for attempt in range(self._config.max_attempts):
            self.stats.bump("attempts")
            try:
                if read:
                    self.stats.bump("reads")
                    return self._read_attempt(actor, cmd)
                return self._write_attempt(actor, cmd, idem)
            except _Failure as f:
                if not f.retryable(keyed):
                    raise f.error() from f
                self.stats.bump("retries")
                time.sleep(_backoff(attempt))
        raise RetriesExhausted()

    def _fire_locked(self, conn: psycopg.Connection[Any], tenant: int) -> None:
        hook = self._config.hook
        if hook is None:
            return
        row = _run(conn, BACKEND_PID).fetchone()
        assert row is not None
        hook(Attempt(Point.LOCKED, tenant, row[0], None))

    def _fire(self, conn: psycopg.Connection[Any], point: Point, tenant: int) -> None:
        hook = self._config.hook
        if hook is None:
            return
        row = _run(conn, TX_INFO).fetchone()
        assert row is not None
        tx = TxInfo(
            vxid=row[4],
            isolation=row[1],
            read_only=row[2] == "on",
            deferrable=row[3] == "on",
        )
        hook(Attempt(point, tenant, row[0], tx))

    def _load(
        self, conn: psycopg.Connection[Any], tv: int
    ) -> list[list[list[sql.Val]]]:
        """The rows of every table for the tenant, by the generated `select`."""
        everything = []
        for t in range(len(self._tables)):
            compiled = sql.select(self._tables, tv, t, None)
            if compiled is None:
                raise _broken("a table has no SELECT")
            q, ps = compiled
            cursor = _run(conn, sql.render(q), _params(ps))
            everything.append([_values(cursor, row) for row in cursor.fetchall()])
        return everything

    def _snapshot(
        self, conn: psycopg.Connection[Any], tenant: int, tv: int
    ) -> tuple[int, Any]:
        """The tenant's version, and the snapshot remembered for it or else the one `load` builds
        of the rows of every table."""
        row = _run(conn, VERSION, [tv]).fetchone()
        version = 0 if row is None else row[0]
        snap = self._cache.take(tenant, version)
        if snap is not None:
            return version, snap
        self.stats.bump("loads")
        snap = self._storage.load(self._load(conn, tv))
        if snap is None:
            raise _broken("the stored rows do not load")
        return version, snap

    def _decide(
        self, tv: int, snap: Any, actor: Any, cmd: Any
    ) -> _Refusal | tuple[list[tuple[str, list[Any]]], Any, Any]:
        """Runs the command on the snapshot and compiles its writes. An accepted command gives
        the snapshot `apply` computed, which the engine owns from then on."""
        try:
            ws, reply = self._kernel.transition(actor, snap, cmd)
        except Refused as e:
            return _Refusal(e)
        writes = self._storage.writes(ws)
        applied = self._kernel.apply(snap, ws)
        statements = []
        for write in writes:
            compiled = sql.compile(self._tables, tv, sql.plan(write))
            if compiled is None:
                raise _broken("a write does not compile")
            q, ps = compiled
            statements.append((sql.render(q), _params(ps)))
        return statements, reply, applied

    def _write_attempt(self, actor: Any, cmd: Any, idem: _Idempotency | None) -> Any:
        """One attempt on a connection of its own, returned to the pool only when it ended
        without a failure and holds no advisory lock."""
        tenant = self._kernel.tenant(actor)
        tv = _signed(tenant)
        conn = self._pool.get()
        ended = False
        try:
            if self._config.tenant_lock:
                _run(conn, TENANT_LOCK, [tv])
            self._fire_locked(conn, tenant)
            result = self._transact(conn, actor, cmd, idem, tenant, tv)
            ended = True
            return result
        finally:
            unlocked = self._release(conn)
            self._pool.put(conn, ended and unlocked)

    def _release(self, conn: psycopg.Connection[Any]) -> bool:
        """Ends a transaction left open by a failure and releases the advisory locks."""
        if conn.closed:
            return False
        try:
            if conn.info.transaction_status != TransactionStatus.IDLE:
                conn.execute(ROLLBACK, prepare=False)
            if self._config.tenant_lock:
                conn.execute(UNLOCK_ALL, prepare=False)
        except psycopg.Error:
            return False
        return True

    def _transact(
        self,
        conn: psycopg.Connection[Any],
        actor: Any,
        cmd: Any,
        idem: _Idempotency | None,
        tenant: int,
        tv: int,
    ) -> Any:
        _run(conn, BEGIN_WRITE)
        if idem is not None:
            row = _run(conn, STORED_REPLY, [tv, idem.scope, idem.key]).fetchone()
            if row is not None:
                fingerprint, stored = row
                if bytes(fingerprint) != idem.fingerprint:
                    _run(conn, ROLLBACK)
                    raise _Final(IdempotencyConflict())
                reply = self._storage.decode_reply(bytes(stored))
                if reply is None:
                    raise _broken("a stored reply does not decode")
                _run(conn, ROLLBACK)
                self.stats.bump("replays")
                return reply
        version, snap = self._snapshot(conn, tenant, tv)
        self._fire(conn, Point.LOADED, tenant)
        decided = self._decide(tv, snap, actor, cmd)
        if isinstance(decided, _Refusal):
            self._cache.put(tenant, version, snap)
            _run(conn, ROLLBACK)
            return decided
        statements, reply, snap = decided
        for text, ps in statements:
            _run(conn, text, ps)
        if statements:
            advanced = _run(conn, ADVANCE, [tv]).fetchone()
            assert advanced is not None
            version = advanced[0]
        if idem is not None:
            stored = self._storage.encode_reply(reply)
            _run(
                conn,
                STORE_REPLY,
                [tv, idem.scope, idem.key, idem.fingerprint, stored],
            )
        self._fire(conn, Point.WRITTEN, tenant)
        _commit(conn)
        self._cache.put(tenant, version, snap)
        self.stats.bump("commits")
        return reply

    def _read_attempt(self, actor: Any, cmd: Any) -> Any:
        tenant = self._kernel.tenant(actor)
        tv = _signed(tenant)
        conn = self._pool.get()
        ended = False
        try:
            result = self._read_transact(conn, actor, cmd, tenant, tv)
            ended = True
            return result
        finally:
            if not ended and not conn.closed:
                try:
                    if conn.info.transaction_status != TransactionStatus.IDLE:
                        conn.execute(ROLLBACK, prepare=False)
                except psycopg.Error:
                    pass
            self._pool.put(conn, ended)

    def _read_transact(
        self, conn: psycopg.Connection[Any], actor: Any, cmd: Any, tenant: int, tv: int
    ) -> Any:
        _run(conn, BEGIN_READ)
        version, snap = self._snapshot(conn, tenant, tv)
        self._fire(conn, Point.LOADED, tenant)
        decided = self._decide(tv, snap, actor, cmd)
        if isinstance(decided, _Refusal):
            self._cache.put(tenant, version, snap)
            _run(conn, ROLLBACK)
            return decided
        statements, reply, snap = decided
        if statements:
            _run(conn, ROLLBACK)
            raise _broken("a read-only command wrote")
        self._cache.put(tenant, version, snap)
        _run(conn, COMMIT)
        self.stats.bump("commits")
        return reply


_ROLE = re.compile(r"[a-z_][a-z0-9_]*")


def _role(name: str) -> str:
    if len(name) <= 63 and _ROLE.fullmatch(name):
        return name
    raise Broken(f"the role name {name!r} is not [a-z_][a-z0-9_]*")


def lockdown(storage: Storage, admin_url: str, owner: str, engine_role: str) -> None:
    """Run by an administrator of the database: creates the tables of `storage` and the
    framework's tables, makes `owner` own them, and lets `engine_role` read and write their rows
    and nothing else: it cannot alter, drop or truncate them. `owner` is created without the
    right to log in if it does not exist. `engine_role` must exist and may not be a superuser; it
    gets `USAGE` and `CREATE` on the schema, so that the engine's `CREATE TABLE IF NOT EXISTS` at
    start finds the tables."""
    owner, engine = _role(owner), _role(engine_role)
    if owner == engine:
        raise Broken("the owner and the engine's role must differ")
    tables = storage.tables()
    if not sql.valid(tables):
        raise Broken("the tables are not valid")
    try:
        with psycopg.connect(
            admin_url,
            autocommit=True,
            cursor_factory=psycopg.RawCursor,
            context=_ADAPTERS,
        ) as admin:
            row = admin.execute(
                "SELECT rolsuper FROM pg_roles WHERE rolname = $1", [engine]
            ).fetchone()
            if row is None:
                raise Broken(f"the role {engine} does not exist")
            if row[0]:
                raise Broken(f"the role {engine} is a superuser")
            admin.execute(
                "DO $$ BEGIN IF NOT EXISTS (SELECT 1 FROM pg_roles WHERE rolname = "
                f"'{owner}') THEN CREATE ROLE \"{owner}\" NOLOGIN; END IF; END $$",
                prepare=False,
            )
            row = admin.execute(
                "SELECT rolcanlogin FROM pg_roles WHERE rolname = $1", [owner]
            ).fetchone()
            if row is None or row[0]:
                raise Broken(f"the role {owner} can log in")
            _create(admin, tables)
            for name in [*FRAMEWORK_TABLES, *(t.name for t in tables)]:
                q = sql.quote(name)
                admin.execute(
                    f'ALTER TABLE {q} OWNER TO "{owner}"; REVOKE ALL ON {q} FROM PUBLIC; '
                    f'REVOKE ALL ON {q} FROM "{engine}"; '
                    f'GRANT SELECT, INSERT, UPDATE, DELETE ON {q} TO "{engine}"',
                    prepare=False,
                )
            admin.execute(
                "DO $$ BEGIN EXECUTE format('GRANT USAGE, CREATE ON SCHEMA %I TO %I', "
                f"current_schema(), '{engine}'); END $$",
                prepare=False,
            )
    except psycopg.Error as e:
        raise DatabaseError(str(e)) from e
