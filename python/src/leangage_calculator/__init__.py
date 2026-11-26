"""The calculator: the kernel is `lean/Calculator/Kernel.lean`, its table
`lean/Calculator/Store.lean` and its requests and responses `lean/Calculator/Wire.lean`,
generated to `kernel.py`, `store.py` and `wire.py`. `API` is the functions of `wire`."""

from typing import Any, NamedTuple

from leanfran import Err, Local, Ok
from leangage import Api, Kernel, Refused, Storage, http_format

from leangage_calculator import kernel, store, wire


def _transition(
    actor: kernel.Principal, snap: Local | kernel.Snapshot, cmd: kernel.Command
) -> tuple[kernel.Memory | None, kernel.Reply]:
    result = kernel.transition.local(actor, snap, cmd).get()
    if isinstance(result, Err):
        raise Refused(result.error)
    return result.value


def _apply(snap: Local | kernel.Snapshot, write: kernel.Memory | None) -> Local:
    """`apply` on the only reference to a local snapshot, which Lean updates in place, or on the
    snapshot `store.load` built."""
    return kernel.apply.local(snap.take() if isinstance(snap, Local) else snap, write)


KERNEL = Kernel(
    init=kernel.init.local,
    tenant=lambda actor: kernel.tenant.lean(actor).get(),
    transition=_transition,
    apply=_apply,
    read_only=lambda cmd: kernel.readOnly.lean(cmd).get(),
)


def _decode_reply(stored: bytes) -> kernel.Reply | None:
    if len(stored) != 8:
        return None
    return kernel.Reply(v=int.from_bytes(stored, "big"))


STORAGE = Storage(
    kernel=KERNEL,
    tables=store.tables,
    load=store.load,
    writes=store.writes,
    encode_reply=lambda reply: reply.v.to_bytes(8, "big"),
    decode_reply=_decode_reply,
)


class Call(NamedTuple):
    """What the engine runs: the principal and the command, each kept as a Lean value."""

    actor: Any
    cmd: Any


def _request(
    tenant: int, user: int, expiry: int, now: int, body: http_format.Body
) -> Ok[Call] | Err[http_format.Response]:
    """`wire.request`, its result taken apart by `answerOf`, `actorOf` and `cmdOf`, so that the
    call reaches the kernel without a conversion to Python values and back."""
    result = wire.request.lean(tenant, user, expiry, now, body)
    answer = wire.answerOf.lean(result).get()
    if answer is not None:
        return Err(error=answer)
    return Ok(value=Call(wire.actorOf.lean(result), wire.cmdOf.lean(result)))


API = Api(
    request=_request,
    respond=wire.respond,
    fingerprint=lambda cmd: wire.fingerprint.lean(cmd).get(),
    scope=lambda actor: wire.scope.lean(actor).get(),
)
