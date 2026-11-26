"""`POST /rpc` answers each failure of the engine with the status and body of the Rust server."""

import time
from typing import Any

from leangage import (
    Api,
    Broken,
    Claims,
    CommitUnknown,
    DatabaseError,
    IdempotencyConflict,
    RetriesExhausted,
    Verifier,
    issue,
)
from leangage.http import handle

SECRET = b"secret"


class Failing:
    """An engine whose every request fails with `error`."""

    def __init__(self, error: Exception) -> None:
        self.error = error

    def execute(self, actor: Any, cmd: Any) -> Any:
        raise self.error

    def execute_idempotent(
        self, actor: Any, scope: str, key: str, fingerprint: bytes, cmd: Any
    ) -> Any:
        raise self.error


API = Api(
    principal=lambda tenant, user: (tenant, user),
    decode_command=lambda body: body,
    encode_reply=lambda reply: b"",
    encode_error=lambda error: (422, b""),
    fingerprint=lambda cmd: b"",
    scope=lambda actor: "",
)


def test_engine_failures_have_the_statuses_of_the_rust_shell() -> None:
    token = issue(SECRET, Claims(1, 1, int(time.time()) + 600))
    headers = {"Authorization": f"Bearer {token}"}
    for error, status, body in [
        (IdempotencyConflict(), 422, b'{"error":"idempotency key reused"}'),
        (RetriesExhausted(), 503, b'{"error":"retries exhausted"}'),
        (DatabaseError("x"), 503, b'{"error":"database error"}'),
        (CommitUnknown(), 500, b'{"error":"commit outcome unknown"}'),
        (Broken("x"), 500, b'{"error":"engine error"}'),
    ]:
        answer = handle(Failing(error), API, Verifier(SECRET), headers, b"{}")
        assert answer == (status, body), error
