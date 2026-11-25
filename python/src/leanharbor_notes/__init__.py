"""The notes: the kernel is `lean/Notes/Kernel.lean`, generated to `kernel.py`.

Its `transition` is the kernel's `handle` behind the guard of `lean/Leanharbor/Authz.lean`.
"""

from leanfran import Err, Local
from leanharbor import Kernel, Refused

from leanharbor_notes import kernel

Guarded = kernel.Leanharbor_Authz_Guarded_Notes_Kernel_Error


def refusal_name(refusal: Guarded) -> str:
    """The name of a refusal: the guard's, or the kernel's."""
    match refusal:
        case kernel.Leanharbor_Authz_Guarded_Notes_Kernel_Error_denied():
            return "denied"
        case kernel.Leanharbor_Authz_Guarded_Notes_Kernel_Error_app(
            e=kernel.Error.notFound
        ):
            return "not_found"
        case kernel.Leanharbor_Authz_Guarded_Notes_Kernel_Error_app(
            e=kernel.Error.badText
        ):
            return "bad_text"
    raise ValueError(refusal)


def _transition(
    actor: kernel.Principal, snap: Local, cmd: kernel.Command
) -> tuple[list[kernel.Write], kernel.Reply]:
    result = kernel.transition.local(actor, snap, cmd).get()
    if isinstance(result, Err):
        raise Refused(result.error)
    return result.value


KERNEL = Kernel(
    init=kernel.init.local,
    tenant=kernel.tenant,
    transition=_transition,
    apply=lambda snap, writes: kernel.apply.local(snap.take(), writes),
)
