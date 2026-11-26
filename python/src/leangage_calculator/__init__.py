"""The calculator: the kernel is `lean/Calculator/Kernel.lean`, its table
`lean/Calculator/Store.lean` and its requests and responses `lean/Calculator/Wire.lean`,
generated to `kernel.py`, `store.py` and `wire.py`. `API` is the functions of `wire`."""

from leanfran import Err, Local
from leangage import Api, Kernel, Refused, Storage

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
    tenant=kernel.tenant,
    transition=_transition,
    apply=_apply,
    read_only=kernel.readOnly,
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


API = Api(
    request=wire.request,
    respond=wire.respond,
    fingerprint=wire.fingerprint,
    scope=wire.scope,
)
