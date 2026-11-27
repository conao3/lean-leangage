"""The HTTP server: `POST /rpc` answered by `leangage.http.handle`, and `GET /healthz`."""

from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any

from leangage.engine import Engine
from leangage.http import Api, handle
from leangage.token import Verifier


def serve(
    engine: Engine, api: Api, secret: bytes, host: str, port: int
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
            answer = handle(engine, api, verifier, self.headers, body)
            self._send(answer.status, bytes(answer.body), "application/json")

        def log_message(self, format: str, *args: Any) -> None:
            pass

    return ThreadingHTTPServer((host, port), Handler)
