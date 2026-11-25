"""The contract of a kernel and of its storage, and an engine that keeps every tenant's snapshot
in this process."""

import threading
from collections.abc import Callable
from dataclasses import dataclass, field
from typing import Any, Protocol


@dataclass(frozen=True)
class Kernel:
    """The contract of `Leanharbor.Kernel`, filled with functions generated from Lean.

    `transition` returns the writes and the reply of an accepted command, or raises `Refused`.
    `read_only` says whether a command only reads: `ReadOnlySound` says it then writes nothing.
    """

    init: Callable[[], Any]
    tenant: Callable[[Any], int]
    transition: Callable[[Any, Any, Any], tuple[Any, Any]]
    apply: Callable[[Any, Any], Any]
    read_only: Callable[[Any], bool]


@dataclass(frozen=True)
class Storage:
    """The contract of `Leanharbor.Storage`: how a kernel's snapshots are stored in PostgreSQL,
    filled with functions generated from Lean, and the bytes an engine stores for a reply under an
    idempotency key.

    `tables` gives the tables in the order `load` receives their rows. `load` gives the snapshot
    `kernel.transition` takes, or `None` when a row is not one the kernel stores. `writes` gives
    the rows a write set stores. `encode_reply` is trusted: no theorem covers it. `decode_reply`
    gives the reply `encode_reply` stored, or `None` for bytes it does not write.
    """

    kernel: Kernel
    tables: Callable[[], list[Any]]
    load: Callable[[list[list[list[Any]]]], Any | None]
    writes: Callable[[Any], list[Any]]
    encode_reply: Callable[[Any], bytes]
    decode_reply: Callable[[bytes], Any | None]


class Refused(Exception):
    """The kernel refused the command; nothing is stored."""

    def __init__(self, error: Any) -> None:
        super().__init__(error)
        self.error = error


class EngineError(Exception):
    """The request did not reach the kernel's decision, or its decision was not stored."""


class IdempotencyConflict(EngineError):
    """The idempotency key was used before with another command."""


class RetriesExhausted(EngineError):
    """Every attempt failed to serialize or lost its connection; none committed, except that a
    request with an idempotency key may have committed on an attempt whose COMMIT was lost."""


class CommitUnknown(EngineError):
    """The connection was lost during the COMMIT of a request without an idempotency key: it may
    or may not have committed."""


class DatabaseError(EngineError):
    """The database failed the request, which did not commit."""


class Broken(EngineError):
    """The stored rows or reply do not decode, a write set does not compile, or a read-only
    command wrote. Nothing was committed."""


class Engine(Protocol):
    """Runs one command for its principal's tenant: returns the reply, or raises `Refused` or an
    `EngineError`."""

    def execute(self, actor: Any, cmd: Any) -> Any: ...

    def execute_idempotent(
        self, actor: Any, scope: str, key: str, fingerprint: bytes, cmd: Any
    ) -> Any: ...


@dataclass
class MemoryEngine:
    kernel: Kernel
    _tenants: dict[int, Any] = field(default_factory=dict)
    _replies: dict[tuple[int, str, str], tuple[bytes, Any]] = field(
        default_factory=dict
    )
    _lock: threading.Lock = field(default_factory=threading.Lock)

    def _run(self, actor: Any, cmd: Any) -> Any:
        tenant = self.kernel.tenant(actor)
        snap = self._tenants[tenant] if tenant in self._tenants else self.kernel.init()
        writes, reply = self.kernel.transition(actor, snap, cmd)
        self._tenants[tenant] = self.kernel.apply(snap, writes)
        return reply

    def execute(self, actor: Any, cmd: Any) -> Any:
        with self._lock:
            return self._run(actor, cmd)

    def execute_idempotent(
        self, actor: Any, scope: str, key: str, fingerprint: bytes, cmd: Any
    ) -> Any:
        """Runs the command once per `(tenant, scope, key)`; refusals are not stored."""
        with self._lock:
            slot = (self.kernel.tenant(actor), scope, key)
            if slot in self._replies:
                stored, reply = self._replies[slot]
                if stored != fingerprint:
                    raise IdempotencyConflict
                return reply
            reply = self._run(actor, cmd)
            self._replies[slot] = (fingerprint, reply)
            return reply
