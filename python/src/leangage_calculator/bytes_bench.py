"""Times the byte functions the servers call on every request.

(a) the check of one token (split and HMAC), (b) the bytes of one calculator reply and (c) the
bytes of a notes list of 20 notes with bodies of 200 bytes. Each line times the functions over
lists (`parse`, `encodeReply`, `write`) and the functions the servers call (`parseString`,
`encodeReplyArray`, `writeArray`) in alternating rounds.
"""

import hashlib
import hmac
import time
from collections.abc import Callable

from leangage import json_format, token, token_format

from leangage_calculator import API, kernel

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
) -> None:
    old, new = [], []
    for _ in range(ROUNDS):
        old.append(per_op(iterations, lists))
        new.append(per_op(iterations, arrays))
    print(f"{label:<22} lists {show(old)}  arrays {show(new)}")


def verify_lists(secret: bytes, tok: str, now: int) -> token.Claims | None:
    """`token.verify` with `parse` in place of `parseString`."""
    parsed = token_format.parse(list(tok.encode()))
    if parsed is None:
        return None
    tag = hmac.new(secret, bytes(parsed.payload), hashlib.sha256).digest()
    if not hmac.compare_digest(tag, bytes(parsed.sig)) or parsed.exp < now:
        return None
    return token.Claims(parsed.tenant, parsed.user, parsed.exp)


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
    assert verify_lists(secret, tok, 0) == claims == token.verify(secret, tok, 0)
    compare(
        "(a) token check",
        1_000,
        lambda: verify_lists(secret, tok, 0),
        lambda: token.verify(secret, tok, 0),
    )
    compare(
        "    split only",
        1_000,
        lambda: token_format.parse(list(tok.encode())),
        lambda: token_format.parseString(tok),
    )
    payload = tok[: tok.rindex(".")].encode()
    hmac_only = [
        per_op(20_000, lambda: hmac.new(secret, payload, hashlib.sha256).digest())
        for _ in range(ROUNDS)
    ]
    print(f"    HMAC only               {show(hmac_only)}")

    reply = kernel.Reply(v=6)
    assert bytes(kernel.encodeReply(reply)) == API.encode_reply(reply) == b'{"value":6}'
    compare(
        "(b) calculator reply",
        5_000,
        lambda: bytes(kernel.encodeReply(reply)),
        lambda: API.encode_reply(reply),
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


if __name__ == "__main__":
    main()
