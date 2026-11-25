"""`POST /rpc`: one kernel command per request, with the status codes of the Rust shell.

The `{"error": ...}` bodies are written by `leanharbor.json_format.writeArray`, the JSON writer
generated from `lean/Leanharbor/Json.lean`.
"""

import json
import time
from collections.abc import Callable
from dataclasses import dataclass
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any

from leanharbor import json_format
from leanharbor.engine import IdempotencyConflict, MemoryEngine, Refused
from leanharbor.token import TokenError, Verifier


@dataclass(frozen=True)
class Api:
    """How commands, replies and refusals appear on the wire. Trusted: no theorem covers it.

    `encode_reply` and `encode_error` return the bytes of the body.
    """

    principal: Callable[[int, int], Any]
    decode_command: Callable[[Any], Any]
    encode_reply: Callable[[Any], bytes]
    encode_error: Callable[[Any], tuple[int, bytes]]
    fingerprint: Callable[[Any], bytes]
    scope: Callable[[Any], str]


def error_body(message: str) -> bytes:
    """`{"error": message}`, with `?` for a character that is not in UTF-8 (a lone surrogate)."""
    return bytes(
        json_format.writeArray(
            [
                json_format.StrTok_objOpen(),
                json_format.StrTok_key(s="error"),
                json_format.StrTok_str(s=message.encode(errors="replace").decode()),
                json_format.StrTok_objClose(),
            ]
        )
    )


def handle(
    engine: MemoryEngine, api: Api, verifier: Verifier, headers: Any, body: bytes
) -> tuple[int, bytes]:
    authorization = headers.get("Authorization")
    if authorization is None:
        return HTTPStatus.UNAUTHORIZED, error_body("missing authorization header")
    if not authorization.startswith("Bearer "):
        return HTTPStatus.UNAUTHORIZED, error_body(
            "authorization is not a bearer token"
        )
    try:
        claims = verifier.verify(
            authorization.removeprefix("Bearer "), int(time.time())
        )
    except TokenError as e:
        return HTTPStatus.UNAUTHORIZED, error_body(str(e))
    actor = api.principal(claims.tenant, claims.user)
    try:
        cmd = api.decode_command(json.loads(body))
    except ValueError as e:
        return HTTPStatus.BAD_REQUEST, error_body(str(e))
    key = headers.get("Idempotency-Key")
    try:
        if key is None:
            reply = engine.execute(actor, cmd)
        else:
            reply = engine.execute_idempotent(
                actor, api.scope(actor), key, api.fingerprint(cmd), cmd
            )
    except Refused as e:
        return api.encode_error(e.error)
    except IdempotencyConflict:
        return HTTPStatus.UNPROCESSABLE_ENTITY, error_body("idempotency key reused")
    return HTTPStatus.OK, api.encode_reply(reply)


def serve(
    engine: MemoryEngine, api: Api, secret: bytes, host: str, port: int
) -> ThreadingHTTPServer:
    verifier = Verifier(secret)

    class Handler(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"
        wbufsize = -1

        def _send(self, status: int, text: bytes, content_type: str) -> None:
            self.send_response(status)
            self.send_header("Content-Type", content_type)
            self.send_header("Content-Length", str(len(text)))
            self.end_headers()
            self.wfile.write(text)

        def do_GET(self) -> None:
            if self.path == "/healthz":
                self._send(HTTPStatus.OK, b"ok", "text/plain")
            else:
                self._send(HTTPStatus.NOT_FOUND, b"", "text/plain")

        def do_POST(self) -> None:
            body = self.rfile.read(int(self.headers.get("Content-Length", "0")))
            if self.path != "/rpc":
                self._send(HTTPStatus.NOT_FOUND, b"", "text/plain")
                return
            status, text = handle(engine, api, verifier, self.headers, body)
            self._send(status, text, "application/json")

        def log_message(self, format: str, *args: Any) -> None:
            pass

    return ThreadingHTTPServer((host, port), Handler)
