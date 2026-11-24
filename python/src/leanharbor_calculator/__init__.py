"""The calculator: the kernel is `lean/Calculator/Kernel.lean`, generated to `kernel.py`."""

from http import HTTPStatus
from typing import Any

from leanfran import Err, Lean
from leanharbor import Api, Kernel, Refused

from leanharbor_calculator import kernel

_ERRORS = {
    kernel.Error.overflow: "overflow",
    kernel.Error.underflow: "underflow",
    kernel.Error.divByZero: "division_by_zero",
}


def _transition(
    actor: kernel.Principal, snap: Lean[kernel.Snapshot], cmd: kernel.Command
) -> tuple[kernel.Memory | None, kernel.Reply]:
    result = kernel.transition.lean(actor, snap, cmd).get()
    if isinstance(result, Err):
        raise Refused(result.error)
    return result.value


KERNEL = Kernel(
    init=kernel.init.lean,
    tenant=kernel.tenant,
    transition=_transition,
    apply=kernel.apply.lean,
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


API = Api(
    principal=lambda tenant, user: kernel.Principal(org=tenant, user=user),
    decode_command=decode_command,
    encode_reply=lambda reply: {"value": reply.v},
    encode_error=lambda error: (
        HTTPStatus.UNPROCESSABLE_ENTITY,
        {"error": _ERRORS[error]},
    ),
    fingerprint=lambda cmd: repr(cmd).encode(),
    scope=lambda actor: f"u{actor.user}",
)
