"""The calculator: the kernel is `lean/Calculator/Kernel.lean` and its table
`lean/Calculator/Store.lean`, generated to `kernel.py` and `store.py`."""

from http import HTTPStatus
from typing import Any

from leanfran import Err, Local
from leangage import Api, Kernel, Refused, Storage

from leangage_calculator import kernel, store


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


def _number(body: dict[str, Any], name: str) -> int:
    value = body[name]
    if type(value) is not int or not 0 <= value < 2**64:
        raise ValueError(f"`{name}` must be an integer below 2^64")
    return value


def decode_command(body: Any) -> kernel.Command:
    if not isinstance(body, dict) or "cmd" not in body:
        raise ValueError("missing field `cmd`")
    fields = set(body) - {"cmd"}
    match body["cmd"]:
        case "set" if fields == {"value"}:
            return kernel.Command_set(value=_number(body, "value"))
        case "apply" if fields == {"op", "arg"} and body["op"] in (
            "add",
            "sub",
            "mul",
            "div",
        ):
            return kernel.Command_apply(
                op=kernel.Op(body["op"]), arg=_number(body, "arg")
            )
        case "get" if not fields:
            return kernel.Command_get()
    raise ValueError("not a calculator command")


def fingerprint(cmd: kernel.Command) -> bytes:
    """The command as the Rust calculator writes it (its `Debug` form), so that a key stored by
    either server is replayed by the other."""
    match cmd:
        case kernel.Command_set(value=value):
            return f"Set {{ value: {value} }}".encode()
        case kernel.Command_apply(op=op, arg=arg):
            return f"Apply {{ op: {op.value.capitalize()}, arg: {arg} }}".encode()
        case kernel.Command_get():
            return b"Get"
    raise ValueError(cmd)


API = Api(
    principal=lambda tenant, user: kernel.Principal(org=tenant, user=user),
    decode_command=decode_command,
    encode_reply=lambda reply: bytes(kernel.encodeReplyArray(reply)),
    encode_error=lambda error: (
        HTTPStatus.UNPROCESSABLE_ENTITY,
        bytes(kernel.encodeErrorArray(error)),
    ),
    fingerprint=fingerprint,
    scope=lambda actor: f"u{actor.user}",
)
