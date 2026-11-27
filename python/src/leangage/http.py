"""`POST /rpc`: one kernel command per request.

`handle` passes the request to generated functions and returns what they return. It gives the
`Authorization` header to `Verifier.admit`, which calls `leangage.gen.http_format.authenticate` and
checks the tag; it gives the claims, the time and the body to `Api.request`; it runs the command
on the engine; and it gives the kernel's decision to `Api.respond` and a failure of the engine to
`leangage.gen.http_format.failed`. The status and the body of every answer come from those
functions, which are generated from `lean/Leangage/Http.lean` and from the kernel's module beside
it (`lean/Calculator/Wire.lean`).
"""

import time
from collections.abc import Callable
from dataclasses import dataclass
from typing import Any

from leanfran import Err, Ok

from leangage.engine import (
    Broken,
    CommitUnknown,
    DatabaseError,
    Engine,
    EngineError,
    IdempotencyConflict,
    Refused,
    RetriesExhausted,
)
from leangage.gen import http_format
from leangage.json_text import tokens
from leangage.token import Claims, Verifier


@dataclass(frozen=True)
class Api:
    """A kernel's functions on the wire, each a function generated from Lean.

    `request` takes the tenant, the user and the expiry a checked token claims, the time and the
    body, and returns `Ok` of what the engine runs (a value with the fields `actor` and `cmd`)
    or `Err` of the answer. `respond` takes `Ok` of a reply or `Err` of a refusal and returns the
    answer.
    """

    request: Callable[[int, int, int, int, http_format.Body], Any]
    respond: Callable[[Any], http_format.Response]
    fingerprint: Callable[[Any], Any]
    scope: Callable[[Any], str]


FAILURES: list[tuple[type[EngineError], http_format.Failure]] = [
    (IdempotencyConflict, http_format.Failure.conflict),
    (RetriesExhausted, http_format.Failure.retriesExhausted),
    (DatabaseError, http_format.Failure.database),
    (CommitUnknown, http_format.Failure.commitUnknown),
    (Broken, http_format.Failure.broken),
]


def body_of(data: bytes) -> http_format.Body:
    """The body as the generated functions take it."""
    read = tokens(data)
    if read is None:
        return http_format.Body_notJson()
    return http_format.Body_json(packed=read)


def handle(
    engine: Engine, api: Api, verifier: Verifier, headers: Any, body: bytes
) -> http_format.Response:
    claims = verifier.admit(headers.get("Authorization"))
    if not isinstance(claims, Claims):
        return claims
    call = api.request(
        claims.tenant, claims.user, claims.expiry, int(time.time()), body_of(body)
    )
    if isinstance(call, Err):
        return call.error
    actor, cmd = call.value.actor, call.value.cmd
    key = headers.get("Idempotency-Key")
    try:
        if key is None:
            reply = engine.execute(actor, cmd)
        else:
            reply = engine.execute_idempotent(
                actor, api.scope(actor), key, bytes(api.fingerprint(cmd)), cmd
            )
    except Refused as e:
        return api.respond(Err(error=e.error))
    except EngineError as e:
        for kind, failure in FAILURES:
            if isinstance(e, kind):
                return http_format.failed(failure)
        raise
    return api.respond(Ok(value=reply))
