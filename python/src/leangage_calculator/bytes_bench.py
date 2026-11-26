"""Times the byte functions the servers call on every request.

(a) the check of one token (split and HMAC), (b) the bytes of one calculator reply and (c) the
bytes of a notes list of 20 notes with bodies of 200 bytes. Each line times the functions over
lists (`parse`, `encodeReply`, `write`) and the functions over strings and arrays
(`authenticate`, `encodeReplyArray`, `writeArray`) in alternating rounds. (d) times the reading
of one request body into a command, written by hand with `json` and as the calculator server
does it: `json` and `leangage.json_text.tokens` for the tokens, then the generated
`wire.request`. It prints calls per second (higher is better) for a body without spaces and for
the same body as `json.dumps` writes it, and the time of each stage of the server's path. (e)
times the answer to an accepted command, written by hand and as the generated `wire.respond`.
(f) times what the server does for one `POST /rpc` once the request is read from the socket:
`leangage.http.handle` with the `Authorization` header and the body, on the memory engine, for
the bodies `{"cmd":"get"}` and `{"cmd":"apply","op":"div","arg":1}`.
"""

import hashlib
import hmac
import json
import time
from collections.abc import Callable

from leanfran import Ok
from leangage import MemoryEngine, http_format, json_format, token, token_format
from leangage.http import body_of, handle
from leangage.json_text import tokens

from leangage_calculator import API, KERNEL, kernel, wire

ROUNDS = 5


def per_op(iterations: int, f: Callable[[], object]) -> float:
    start = time.perf_counter_ns()
    for _ in range(iterations):
        f()
    return (time.perf_counter_ns() - start) / iterations


def show(rounds: list[float]) -> str:
    rounds.sort()
    return f"{rounds[0]:>11.0f} ns (median {rounds[ROUNDS // 2]:>11.0f})"


def compare(
    label: str,
    iterations: int,
    lists: Callable[[], object],
    arrays: Callable[[], object],
    names: tuple[str, str] = ("lists", "arrays"),
) -> None:
    old, new = [], []
    for _ in range(ROUNDS):
        old.append(per_op(iterations, lists))
        new.append(per_op(iterations, arrays))
    print(f"{label:<22} {names[0]} {show(old)}  {names[1]} {show(new)}")


def verify_lists(secret: bytes, tok: str, now: int) -> token.Claims | None:
    """The check of a token with `parse`, the tag and the expiry, written by hand."""
    parsed = token_format.parse(list(tok.encode()))
    if parsed is None:
        return None
    tag = hmac.new(secret, bytes(parsed.payload), hashlib.sha256).digest()
    if not hmac.compare_digest(tag, bytes(parsed.sig)) or parsed.exp < now:
        return None
    return token.Claims(parsed.tenant, parsed.user, parsed.exp)


def decode_by_hand(body: bytes) -> kernel.Command | None:
    """A body read into a command with `json`, written by hand."""
    fields = json.loads(body)
    if not isinstance(fields, dict):
        return None

    def number(name: str) -> int | None:
        value = fields.get(name)
        return value if type(value) is int and 0 <= value < 2**64 else None

    rest = set(fields) - {"cmd"}
    match fields.get("cmd"):
        case "set" if rest == {"value"} and number("value") is not None:
            return kernel.Command_set(value=number("value"))
        case "apply" if rest == {"op", "arg"} and number("arg") is not None:
            if fields["op"] in ("add", "sub", "mul", "div"):
                return kernel.Command_apply(
                    op=kernel.Op(fields["op"]), arg=number("arg")
                )
        case "get" if not rest:
            return kernel.Command_get()
    return None


def request_rate(form: str, request: bytes, command: kernel.Command) -> None:
    """Calls per second of the reading of one body, by hand and as the server does it."""
    assert (
        decode_by_hand(request)
        == command
        == wire.request(1, 42, 1, 0, body_of(request)).value.cmd
    )
    by_hand, generated = [], []
    for _ in range(ROUNDS):
        by_hand.append(per_op(2_000, lambda: decode_by_hand(request)))
        generated.append(
            per_op(2_000, lambda: wire.request(1, 42, 1, 0, body_of(request)))
        )
    print(
        f"(d) request body, {form:<8} by hand {1e9 / min(by_hand):>9.0f} calls/s  "
        f"library and generated {1e9 / min(generated):>9.0f} calls/s"
    )


NOTES = [(i, 7, i % 2 == 0, "n" * 200) for i in range(20)]


def notes_toks() -> list[json_format.Tok]:
    """The tokens of {"notes":[...]}, in the order the Rust notes server writes, over lists."""
    out: list[json_format.Tok] = [
        json_format.Tok_objOpen(),
        json_format.Tok_key(s=list(b"notes")),
        json_format.Tok_arrOpen(),
    ]
    for i, owner, shared, body in NOTES:
        out += [
            json_format.Tok_objOpen(),
            json_format.Tok_key(s=list(b"body")),
            json_format.Tok_str(s=list(body.encode())),
            json_format.Tok_key(s=list(b"id")),
            json_format.Tok_num(n=i),
            json_format.Tok_key(s=list(b"owner")),
            json_format.Tok_num(n=owner),
            json_format.Tok_key(s=list(b"shared")),
            json_format.Tok_bool(b=shared),
            json_format.Tok_objClose(),
        ]
    return out + [json_format.Tok_arrClose(), json_format.Tok_objClose()]


def notes_str_toks() -> list[json_format.StrTok]:
    """The same tokens, with strings."""
    out: list[json_format.StrTok] = [
        json_format.StrTok_objOpen(),
        json_format.StrTok_key(s="notes"),
        json_format.StrTok_arrOpen(),
    ]
    for i, owner, shared, body in NOTES:
        out += [
            json_format.StrTok_objOpen(),
            json_format.StrTok_key(s="body"),
            json_format.StrTok_str(s=body),
            json_format.StrTok_key(s="id"),
            json_format.StrTok_num(n=i),
            json_format.StrTok_key(s="owner"),
            json_format.StrTok_num(n=owner),
            json_format.StrTok_key(s="shared"),
            json_format.StrTok_bool(b=shared),
            json_format.StrTok_objClose(),
        ]
    return out + [json_format.StrTok_arrClose(), json_format.StrTok_objClose()]


def main() -> None:
    secret = b"bench-secret"
    claims = token.Claims(tenant=1, user=42, expiry=4_102_444_800)
    tok = token.issue(secret, claims)
    header = f"Bearer {tok}"
    assert verify_lists(secret, tok, 0) == claims == token.admit(secret, header)
    compare(
        "(a) token check",
        1_000,
        lambda: verify_lists(secret, tok, 0),
        lambda: token.admit(secret, header),
    )
    compare(
        "    split only",
        1_000,
        lambda: token_format.parse(list(tok.encode())),
        lambda: http_format.authenticate(header),
    )
    payload = tok[: tok.rindex(".")].encode()
    hmac_only = [
        per_op(20_000, lambda: hmac.new(secret, payload, hashlib.sha256).digest())
        for _ in range(ROUNDS)
    ]
    print(f"    HMAC only               {show(hmac_only)}")

    reply = kernel.Reply(v=6)
    assert bytes(kernel.encodeReply(reply)) == b'{"value":6}'
    assert bytes(kernel.encodeReplyArray(reply)) == b'{"value":6}'
    compare(
        "(b) calculator reply",
        5_000,
        lambda: bytes(kernel.encodeReply(reply)),
        lambda: bytes(kernel.encodeReplyArray(reply)),
    )

    body = bytes(json_format.write(notes_toks()))
    assert body == bytes(json_format.writeArray(notes_str_toks()))
    assert body.startswith(b'{"notes":[{"body":"nnn')
    compare(
        "(c) notes list of 20",
        10,
        lambda: bytes(json_format.write(notes_toks())),
        lambda: bytes(json_format.writeArray(notes_str_toks())),
    )

    command = kernel.Command_apply(op=kernel.Op.mul, arg=7)
    fields = {"cmd": "apply", "op": "mul", "arg": 7}
    request = json.dumps(fields).encode()
    request_rate("compact", json.dumps(fields, separators=(",", ":")).encode(), command)
    request_rate("spaced", request, command)
    text = request.decode()
    read = tokens(request)
    assert read is not None
    body = body_of(request)
    stages: list[tuple[str, Callable[[], object]]] = [
        ("json.loads", lambda: json.loads(text)),
        ("tokens", lambda: tokens(request)),
        ("Body_json", lambda: http_format.Body_json(packed=read)),
        ("parse and conversion", lambda: body_of(request)),
        ("generated request", lambda: wire.request(1, 42, 1, 0, body)),
        ("request.lean", lambda: wire.request.lean(1, 42, 1, 0, body)),
        ("request, token expired", lambda: wire.request(1, 42, 0, 1, body)),
    ]
    for name, stage in stages:
        rounds = [per_op(2_000, stage) for _ in range(ROUNDS)]
        print(f"    {name:<23} {show(rounds)}")
    assert bytes(wire.respond(Ok(value=reply)).body) == b'{"value":6}'
    compare(
        "(e) answer",
        2_000,
        lambda: (200, bytes(kernel.encodeReplyArray(reply))),
        lambda: wire.respond(Ok(value=reply)),
        ("by hand", "generated"),
    )

    engine = MemoryEngine(KERNEL)
    verifier = token.Verifier(secret)
    headers = {"Authorization": header}
    assert (
        bytes(handle(engine, API, verifier, headers, b'{"cmd":"set","value":6}').body)
        == b'{"value":6}'
    )
    for name, rpc in [
        ("get", b'{"cmd":"get"}'),
        ("apply", b'{"cmd":"apply","op":"div","arg":1}'),
    ]:
        assert handle(engine, API, verifier, headers, rpc).status == 200
        rounds = [
            per_op(2_000, lambda rpc=rpc: handle(engine, API, verifier, headers, rpc))
            for _ in range(ROUNDS)
        ]
        label = "(f) rpc handler" if name == "get" else "   "
        print(f"{label:<16} {name:<6} {show(rounds)}  {1e9 / rounds[0]:>8.0f} calls/s")


if __name__ == "__main__":
    main()
