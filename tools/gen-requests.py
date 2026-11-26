"""Writes the lines that the Lean request oracle and the Rust, Python and Go servers all answer.

Deterministic: the same seed and count give the same file. The line format is described in
`lean/RequestOracle.lean`. The texts to read are JSON texts with every spelling of a number, a
string and the space between tokens, and the same texts with a byte removed, inserted or
replaced; the headers are bearer tokens and headers close to one; the bodies are the calculator's
commands with their members in any order, and bodies close to one.
"""

import json
import random
import sys

NUMBERS = [0, 1, 9, 10, 99, 100, 10**19 - 1, 10**19, 2**63, 2**64 - 1]
SPELLINGS = [
    "-0", "-1", "0.0", "6.0", "1.5", "-2.25", "1e3", "1E3", "1e+3", "1e-3", "0e0", "12.5e10",
    "18446744073709551616", "99999999999999999999", "100000000000000000000",
    "123456789012345678901234567890", "-18446744073709551615", "1e400", "0.000000000000000000001",
]  # fmt: skip
BROKEN = [
    "", " ", "01", "00", "-", "-a", "1.", ".5", "1e", "1e+", "+1", "0x10", "1.e3", "--1", "1.2.3",
    "tru", "truee", "nul", "nulll", "fals", "True", "NaN", "Infinity", "[1,]", "[,1]", "[1 2]",
    "[", "]", "{", "}", "{,}", '{"a"}', '{"a":}', '{"a":1,}', '{"a" 1}', '{1:2}', '{"a":1 "b":2}',
    '"abc', '"a\nb"', '"\\x41"', '"\\u12"', '"\\u12g4"', '"\\ud800"', '"\\udc00"',
    '"\\ud800\\u0041"', '"\\ud800x"', '"\\udbff\\udbff"', "[1]]", "{}{}", "1 2", '{"a":1}}',
    "﻿1", "'a'", "[1,2", '{"a":[}', "\x00", '"\x1f"', "/**/1", "[1,\n]", '"\\"',
]  # fmt: skip
ESCAPES = [
    '\\"', "\\\\", "\\/", "\\b", "\\f", "\\n", "\\r", "\\t", "\\u0000", "\\u001f", "\\u0041",
    "\\u00e9", "\\u00E9", "\\u07ff", "\\u0800", "\\u20ac", "\\ud7ff", "\\ue000", "\\uffff",
    "\\ud83d\\ude00", "\\uD800\\uDC00", "\\udbff\\udfff",
]  # fmt: skip
PLAIN = [
    "a",
    "cmd",
    " ",
    "é",
    "日本",
    "😀",
    "/",
    ":",
    ",",
    "[",
    "{",
    "}",
    "]",
    "\x7f",
    "0",
]
SPACE = ["", "", "", " ", "\n", "\t", "\r", "  ", " \n "]
OPS = ["add", "sub", "mul", "div"]
REFUSALS = ["overflow", "underflow", "division_by_zero"]
FAILURES = [
    "bad_signature", "conflict", "stopped", "retries_exhausted", "database", "commit_unknown",
    "broken",
]  # fmt: skip


def hexed(data: bytes) -> str:
    return "x" + data.hex()


def number(rng: random.Random) -> int:
    return rng.choice(NUMBERS) if rng.randrange(2) else rng.randrange(1000)


def string(rng: random.Random) -> bytes:
    out = b""
    for _ in range(rng.randrange(6)):
        match rng.randrange(4):
            case 0:
                out += rng.choice(ESCAPES).encode()
            case 1:
                out += rng.choice(PLAIN).encode()
            case 2:
                out += bytes(
                    [rng.choice([0x80, 0xC3, 0xFF, rng.randrange(0x80, 0x100)])]
                )
            case _:
                out += bytes(
                    [rng.choice([c for c in range(32, 127) if c not in (34, 92)])]
                )
    return b'"' + out + b'"'


def scalar(rng: random.Random) -> bytes:
    match rng.randrange(7):
        case 0:
            return b"null"
        case 1:
            return rng.choice([b"true", b"false"])
        case 2 | 3:
            return str(number(rng)).encode()
        case 4:
            return rng.choice(SPELLINGS).encode()
        case _:
            return string(rng)


def value(rng: random.Random, depth: int) -> bytes:
    def ws() -> bytes:
        return rng.choice(SPACE).encode()

    if depth == 0 or rng.randrange(3) == 0:
        return scalar(rng)
    n = rng.randrange(4)
    if rng.randrange(2):
        items = [ws() + value(rng, depth - 1) + ws() for _ in range(n)]
        return b"[" + (b",".join(items) if items else ws()) + b"]"
    members = [
        ws() + string(rng) + ws() + b":" + ws() + value(rng, depth - 1) + ws()
        for _ in range(n)
    ]
    return b"{" + (b",".join(members) if members else ws()) + b"}"


def edited(rng: random.Random, data: bytes) -> bytes:
    if not data:
        return b" "
    i = rng.randrange(len(data))
    c = bytes([rng.choice(b'"\\,:[]{}0123456789-+.eEtfn \n\x00\x1f\x80u') or 0])
    match rng.randrange(5):
        case 0:
            return data[:i] + data[i + 1 :]
        case 1:
            return data[:i] + c + data[i:]
        case 2:
            return data[:i] + c + data[i + 1 :]
        case 3:
            return data[:i]
        case _:
            return data + c


def read_line(rng: random.Random) -> str:
    match rng.randrange(10):
        case 0:
            text = rng.choice(BROKEN).encode()
        case 1:
            text = rng.choice(SPACE).encode() + scalar(rng) + rng.choice(SPACE).encode()
        case 2:
            depth = rng.choice([1, 2, 50, 300])
            text = b"[" * depth + scalar(rng) + b"]" * (depth - rng.randrange(2))
        case 3 | 4 | 5:
            text = edited(rng, value(rng, 3))
        case _:
            text = (
                rng.choice(SPACE).encode() + value(rng, 3) + rng.choice(SPACE).encode()
            )
    return f"read {hexed(text)}"


def field(rng: random.Random) -> str:
    match rng.randrange(8):
        case 0:
            return rng.choice(["", "0", "00", "01", "+1", "-1", "18446744073709551616"])
        case 1:
            return str(rng.choice(NUMBERS))
        case _:
            return str(rng.randrange(1000))


def token(rng: random.Random) -> str:
    tag = bytes(rng.randrange(256) for _ in range(rng.choice([32, 32, 32, 0, 1, 31])))
    text = f"v1.{field(rng)}.{field(rng)}.{field(rng)}.{tag.hex()}"
    match rng.randrange(8):
        case 0:
            return edited(rng, text.encode()).decode(errors="replace")
        case 1:
            return text.upper()
        case 2:
            return text + rng.choice([".", ".00", " ", "\n"])
        case _:
            return text


def auth_line(rng: random.Random) -> str:
    match rng.randrange(12):
        case 0:
            return "auth -"
        case 1:
            header = rng.choice(
                ["", "Bearer", "Bearer ", "bearer ", "BEARER ", "Basic ", "Bearer\t"]
            )
            header += rng.choice(["", token(rng)])
        case 2:
            header = rng.choice(
                [" Bearer ", "Bearer  ", "Token ", "Bearer é", "é"]
            ) + token(rng)
        case _:
            header = "Bearer " + token(rng)
    return f"auth {hexed(header.encode())}"


def spelled(rng: random.Random, members: list[tuple[str, str]]) -> str:
    def ws() -> str:
        return rng.choice(SPACE)

    rng.shuffle(members)
    inner = ",".join(f"{ws()}{json.dumps(k)}{ws()}:{ws()}{v}{ws()}" for k, v in members)
    return ws() + "{" + (inner or ws()) + "}" + ws()


def operand(rng: random.Random) -> str:
    match rng.randrange(8):
        case 0:
            return rng.choice(
                SPELLINGS + ["null", "true", '"6"', "[6]", '{"n":6}', '""']
            )
        case _:
            return str(number(rng))


def command_body(rng: random.Random) -> str:
    match rng.randrange(4):
        case 0:
            members = [("cmd", '"set"'), ("value", operand(rng))]
        case 1 | 2:
            members = [
                ("cmd", '"apply"'),
                ("op", json.dumps(rng.choice(OPS))),
                ("arg", operand(rng)),
            ]
        case _:
            members = [("cmd", '"get"')]
    match rng.randrange(14):
        case 0:
            members.append(
                rng.choice(
                    [("value", "6"), ("arg", "1"), ("x", "null"), ("cmd", '"get"')]
                )
            )
        case 1 if members:
            members.pop(rng.randrange(len(members)))
        case 2:
            k, v = members[0]
            members[0] = (rng.choice([k.upper(), k + " ", "c\\u006dd"]), v)
        case 3:
            members = [
                (
                    k,
                    rng.choice(['"pow"', '"Set"', '"gets"', "null", "1", '"ad\\u0064"'])
                    if k in ("cmd", "op")
                    else v,
                )
                for k, v in members
            ]
        case 4:
            return rng.choice(
                [
                    "[]",
                    "null",
                    '"get"',
                    "7",
                    '{"cmd":"get"} x',
                    "{",
                    "",
                    '[{"cmd":"get"}]',
                ]
            )
    text = spelled(rng, members)
    if rng.randrange(20) == 0:
        return text.replace('"cmd"', '"\\u0063md"')
    return text


def request_line(rng: random.Random) -> str:
    exp = rng.choice([0, 1, 100, 2**64 - 1, rng.randrange(1000)])
    now = rng.choice(
        [0, exp, exp + 1 if exp < 2**64 - 1 else exp, rng.randrange(1000), exp, exp]
    )
    match rng.randrange(16):
        case 0:
            body = rng.choice(["notutf8", "toolarge", "unreadable"])
        case _:
            body = hexed(command_body(rng).encode())
    return f"request {number(rng)} {number(rng)} {exp} {now} {body}"


def command(rng: random.Random) -> str:
    match rng.randrange(3):
        case 0:
            return f"set {number(rng)}"
        case 1:
            return f"apply {rng.choice(OPS)} {number(rng)}"
        case _:
            return "get"


def other_line(rng: random.Random) -> str:
    match rng.randrange(6):
        case 0:
            return f"respond ok {number(rng)}"
        case 1:
            return f"respond err {rng.choice(REFUSALS)}"
        case 2:
            return f"failure {rng.choice(FAILURES)}"
        case 3:
            return f"scope {number(rng)}"
        case _:
            return f"fingerprint {command(rng)}"


def main() -> None:
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    rng = random.Random(9124)
    for _ in range(count):
        match rng.randrange(20):
            case n if n < 9:
                print(read_line(rng))
            case n if n < 12:
                print(auth_line(rng))
            case n if n < 18:
                print(request_line(rng))
            case _:
                print(other_line(rng))


main()
