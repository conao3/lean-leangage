"""An engine that keeps every tenant's snapshot in this process."""

import threading
from collections.abc import Callable
from dataclasses import dataclass, field
from typing import Any


@dataclass(frozen=True)
class Kernel:
    """The contract of `Leanharbor.Kernel`, filled with functions generated from Lean.

    `step` returns the writes and the reply of an accepted command, or raises `Refused`.
    """

    init: Callable[[], Any]
    tenant: Callable[[Any], int]
    step: Callable[[Any, Any, Any], tuple[Any, Any]]
    apply: Callable[[Any, Any], Any]


class Refused(Exception):
    """The kernel refused the command; nothing is stored."""

    def __init__(self, error: Any) -> None:
        super().__init__(error)
        self.error = error


class IdempotencyConflict(Exception):
    """The idempotency key was used before with another command."""


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
        writes, reply = self.kernel.step(actor, snap, cmd)
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
