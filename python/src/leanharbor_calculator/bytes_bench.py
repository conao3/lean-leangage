"""Times the byte functions the shells call on every request.

(a) the check of one token (split and HMAC), (b) the bytes of one calculator reply and (c) the
bytes of a notes list of 20 notes with bodies of 200 bytes.
"""

import hashlib
import hmac
import time
from collections.abc import Callable

from leanharbor import json_format, token, token_format

from leanharbor_calculator import API, kernel

ROUNDS = 5


def measure(label: str, iterations: int, f: Callable[[], object]) -> None:
    per_op = []
    for _ in range(ROUNDS):
        start = time.perf_counter_ns()
        for _ in range(iterations):
            f()
        per_op.append((time.perf_counter_ns() - start) / iterations)
    per_op.sort()
    print(
        f"{label:<28} median {per_op[ROUNDS // 2]:>10.0f} ns  min {per_op[0]:>10.0f} ns"
    )


def notes_toks() -> list[json_format.Tok]:
    """The tokens of {"notes":[...]} for 20 notes, in the order the Rust notes shell writes."""
    body = list(b"n" * 200)
    out: list[json_format.Tok] = [
        json_format.Tok_objOpen(),
        json_format.Tok_key(s=list(b"notes")),
        json_format.Tok_arrOpen(),
    ]
    for i in range(20):
        out += [
            json_format.Tok_objOpen(),
            json_format.Tok_key(s=list(b"body")),
            json_format.Tok_str(s=body),
            json_format.Tok_key(s=list(b"id")),
            json_format.Tok_num(n=i),
            json_format.Tok_key(s=list(b"owner")),
            json_format.Tok_num(n=7),
            json_format.Tok_key(s=list(b"shared")),
            json_format.Tok_bool(b=i % 2 == 0),
            json_format.Tok_objClose(),
        ]
    return out + [json_format.Tok_arrClose(), json_format.Tok_objClose()]


def main() -> None:
    secret = b"bench-secret"
    claims = token.Claims(tenant=1, user=42, expiry=4_102_444_800)
    tok = token.issue(secret, claims)
    assert token.verify(secret, tok, 0) == claims
    measure("(a) token verify", 2_000, lambda: token.verify(secret, tok, 0))
    measure("    split only", 2_000, lambda: token_format.parse(list(tok.encode())))
    payload = tok[: tok.rindex(".")].encode()
    measure(
        "    HMAC only",
        20_000,
        lambda: hmac.new(secret, payload, hashlib.sha256).digest(),
    )

    reply = kernel.Reply(v=6)
    assert API.encode_reply(reply) == b'{"value":6}'
    measure("(b) calculator reply", 20_000, lambda: API.encode_reply(reply))

    assert bytes(json_format.write(notes_toks())).startswith(b'{"notes":[{"body":"nnn')
    measure("(c) notes list of 20", 20, lambda: bytes(json_format.write(notes_toks())))


if __name__ == "__main__":
    main()
