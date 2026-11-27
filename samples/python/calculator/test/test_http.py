"""`POST /rpc` answers each request with the status and body of the Rust server."""

import time
from typing import Any

from leangage import (
    Broken,
    Claims,
    CommitUnknown,
    DatabaseError,
    IdempotencyConflict,
    MemoryEngine,
    RetriesExhausted,
    Verifier,
    handle,
    issue,
)
from leangage_calculator import API, KERNEL

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


def post(
    engine: Any, authorization: str | None, body: bytes, key: str | None = None
) -> tuple[int, bytes]:
    headers = {}
    if authorization is not None:
        headers["Authorization"] = authorization
    if key is not None:
        headers["Idempotency-Key"] = key
    answer = handle(engine, API, Verifier(SECRET), headers, body)
    return answer.status, bytes(answer.body)


def bearer(secret: bytes, expiry: int) -> str:
    return f"Bearer {issue(secret, Claims(1, 7, expiry))}"


def test_engine_failures_have_the_statuses_of_the_rust_server() -> None:
    good = bearer(SECRET, int(time.time()) + 600)
    for error, status, body in [
        (IdempotencyConflict(), 422, b'{"error":"idempotency key reused"}'),
        (RetriesExhausted(), 503, b'{"error":"retries exhausted"}'),
        (DatabaseError("x"), 503, b'{"error":"database error"}'),
        (CommitUnknown(), 500, b'{"error":"commit outcome unknown"}'),
        (Broken("x"), 500, b'{"error":"engine error"}'),
    ]:
        assert post(Failing(error), good, b'{"cmd":"get"}') == (status, body), error


def test_statuses_and_bodies() -> None:
    engine = MemoryEngine(KERNEL)
    now = int(time.time())
    good = bearer(SECRET, now + 600)
    not_a_command = b'{"error":"not a calculator command"}'
    bad_value = b'{"error":"`value` must be an integer below 2^64"}'
    for authorization, key, body, status, want in [
        (None, None, b"{", 401, b'{"error":"missing authorization header"}'),
        (good[7:], None, b"{", 401, b'{"error":"authorization is not a bearer token"}'),
        ("Bearer v1.1.1", None, b"{", 401, b'{"error":"malformed token"}'),
        (bearer(b"other", now + 600), None, b"{", 401, b'{"error":"bad token signature"}'),
        (bearer(b"other", 1), None, b"{", 401, b'{"error":"bad token signature"}'),
        (bearer(SECRET, 1), None, b"{", 401, b'{"error":"token expired"}'),
        (good, None, b'{"cmd":"set","value":6}', 200, b'{"value":6}'),
        (good, None, b' { "value" : 7 , "cmd" : "set" } ', 200, b'{"value":7}'),
        (good, None, b'{"cmd":"apply","op":"mul","arg":6}', 200, b'{"value":42}'),
        (good, None, b'{"cmd":"get"}', 200, b'{"value":42}'),
        (good, None, b'{"cmd":"apply","op":"div","arg":0}', 422, b'{"error":"division_by_zero"}'),
        (good, "k", b'{"cmd":"apply","op":"add","arg":1}', 200, b'{"value":43}'),
        (good, "k", b'{"cmd":"apply","op":"add","arg":1}', 200, b'{"value":43}'),
        (good, "k", b'{"cmd":"apply","op":"add","arg":2}', 422, b'{"error":"idempotency key reused"}'),
        (good, None, b"{", 400, b'{"error":"body is not JSON"}'),
        (good, None, b'{"cmd":"get"} x', 400, b'{"error":"body is not JSON"}'),
        (good, None, b"\xff\xfe", 400, b'{"error":"body is not JSON"}'),
        (good, None, b'{"cmd":"set"}', 400, not_a_command),
        (good, None, b'{"cmd":"set","value":6,"arg":1}', 400, not_a_command),
        (good, None, b'{"cmd":"get","cmd":"get"}', 400, not_a_command),
        (good, None, b'{"cmd":"apply","op":"pow","arg":1}', 400, not_a_command),
        (good, None, b"[]", 400, not_a_command),
        (good, None, b'{"CMD":"get"}', 400, b'{"error":"missing field `cmd`"}'),
        (good, None, b'{"cmd":"set","value":6.0}', 400, bad_value),
        (good, None, b'{"cmd":"set","value":18446744073709551616}', 400, bad_value),
        (good, None, b'{"cmd":"apply","op":"add","arg":-1}', 400, b'{"error":"`arg` must be an integer below 2^64"}'),
    ]:  # fmt: skip
        assert post(engine, authorization, body, key) == (status, want), body


def test_a_deep_body_is_refused() -> None:
    """A body of nothing but `[` is answered, and so is one nested 10,000 deep."""
    good = bearer(SECRET, int(time.time()) + 600)
    engine = MemoryEngine(KERNEL)
    assert post(engine, good, b"[" * 20_000) == (400, b'{"error":"body is not JSON"}')
    assert post(engine, good, b"[" * 10_000 + b"]" * 10_000) == (
        400,
        b'{"error":"not a calculator command"}',
    )
