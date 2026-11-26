"""Writes the lines that the Lean request oracle and the Rust, Python and Go servers all answer.

Deterministic: the same seed and count give the same file. The line format is described in
`lean/RequestOracle.lean`. The texts are JSON texts with every spelling of a number, a string and
the space between tokens, and the same texts with a byte removed, inserted or replaced; the
headers are bearer tokens and headers close to one; the bodies are the calculator's commands with
their members in any order, the same commands written without a space with their members in the
order of `cmd`, `value` or `cmd`, `op`, `arg`, and bodies close to one. `library_body` and
`library_text` write the texts on which a JSON library could differ from the grammar: a member
twice, members in another order, the space between tokens, numbers at 2^64, data after the value,
arrays nested 100 deep, `NaN` and `Infinity`, member names in upper case, UTF-16 and a byte order
mark.

Every text is one that serde_json, `encoding/json` and Python's `json` read alike: no escape
of a surrogate outside a pair, no exponent of 3 digits, no nesting above 100. The tests of each
server's conversion hold the texts on which the three differ.
"""

import json
import random
import re
import sys

NUMBERS = [0, 1, 9, 10, 99, 100, 10**19 - 1, 10**19, 2**63, 2**64 - 1]
SPELLINGS = [
    "-0", "-1", "0.0", "6.0", "1.5", "-2.25", "1e3", "1E3", "1e+3", "1e-3", "0e0", "12.5e10",
    "18446744073709551616", "99999999999999999999", "100000000000000000000",
    "123456789012345678901234567890", "-18446744073709551615", "1e30", "0.000000000000000000001",
]  # fmt: skip
BROKEN = [
    "", " ", "01", "00", "-", "-a", "1.", ".5", "1e", "1e+", "+1", "0x10", "1.e3", "--1", "1.2.3",
    "tru", "truee", "nul", "nulll", "fals", "True", "NaN", "Infinity", "[1,]", "[,1]", "[1 2]",
    "[", "]", "{", "}", "{,}", '{"a"}', '{"a":}', '{"a":1,}', '{"a" 1}', '{1:2}', '{"a":1 "b":2}',
    '"abc', '"a\nb"', '"\\x41"', '"\\u12"', '"\\u12g4"', "[1]]", "{}{}", "1 2", '{"a":1}}',
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
COMPACT = random.Random(4219)
LIBRARY = random.Random(5830)
PAIR = re.compile(rb"\\u[dD][89abAB][0-9a-fA-F]{2}\\u[dD][c-fC-F][0-9a-fA-F]{2}")
SURROGATE = re.compile(rb"\\u[dD][89a-fA-F]")
EXPONENT = re.compile(rb"[eE][+-]?[0-9]{3}")
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


def shared(text: bytes) -> bool:
    """Whether the three libraries read or refuse the text alike."""
    return not SURROGATE.search(PAIR.sub(b"", text)) and not EXPONENT.search(text)


def library_text(rng: random.Random) -> bytes:
    deep = b"[" * 100 + rng.choice([b"", b"1", b'"a"', b"{}"]) + b"]" * 100
    return rng.choice(
        [
            b'{"a":1,"a":2}',
            b'{"a":1,"b":2,"a":null}',
            b'{"a":{"a":1,"a":1}}',
            b'{"":1,"":2}',
            b'{"b":1,"a":2}',
            b"18446744073709551615",
            b"18446744073709551616",
            b"[18446744073709551615,18446744073709551616]",
            b"01",
            b"-0",
            b"1.0",
            b"1e2",
            b"1E2",
            b"[0,-0,0.0,0e0]",
            b"00",
            b"-01",
            b"{}{}",
            b"{} {}",
            b"[] 1",
            b"1 2",
            b"[]]",
            b"null,",
            b'"a""b"',
            deep,
            deep[:-1],
            deep + b"]",
            b'{"a":' * 100 + b"1" + b"}" * 100,
            b"NaN",
            b"Infinity",
            b"-Infinity",
            b"[NaN]",
            b'{"a":Infinity}',
            b"nan",
            b'{"CMD":"get"}',
            b'{"Cmd":"get","cmd":"get"}',
            b'{"A":1,"a":2}',
            '{"cmd":"get"}'.encode("utf-16"),
            '{"cmd":"get"}'.encode("utf-16-le"),
            '{"cmd":"get"}'.encode("utf-16-be"),
            "1".encode("utf-16-le"),
            b"\xef\xbb\xbf{}",
            b"\xef\xbb\xbf1",
            b' \t\r\n{ \t\r\n"a" \t\r\n: \t\r\n1 \t\r\n} \t\r\n',
            b"\x0c1",
            b"\xc2\xa01",
            b"[1,\x0b2]",
        ]
    )


def read_line(rng: random.Random) -> str:
    if LIBRARY.randrange(8) == 0:
        return f"items {hexed(library_text(LIBRARY))}"
    while True:
        text = read_text(rng)
        if shared(text):
            return f"items {hexed(text)}"


def read_text(rng: random.Random) -> bytes:
    match rng.randrange(10):
        case 0:
            text = rng.choice(BROKEN).encode()
        case 1:
            text = rng.choice(SPACE).encode() + scalar(rng) + rng.choice(SPACE).encode()
        case 2:
            depth = rng.choice([1, 2, 50, 100])
            text = b"[" * depth + scalar(rng) + b"]" * (depth - rng.randrange(2))
        case 3 | 4 | 5:
            text = edited(rng, value(rng, 3))
        case _:
            text = (
                rng.choice(SPACE).encode() + value(rng, 3) + rng.choice(SPACE).encode()
            )
    return text


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


def compact_body(rng: random.Random) -> str:
    number = rng.choice([operand(rng), operand(rng), "", "01", "007", "6}", "6 "])
    text = rng.choice(
        [
            f'{{"cmd":"set","value":{number}}}',
            f'{{"cmd":"apply","op":"{rng.choice(OPS + ["pow"])}","arg":{number}}}',
            f'{{"cmd":"apply","op":"{rng.choice(OPS)}","arg":{number}}}',
            '{"cmd":"get"}',
        ]
    )
    match rng.randrange(8):
        case 0:
            return text[:-1]
        case 1:
            return text + rng.choice([" ", "}", "\n"])
        case _:
            return text


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


def library_body(rng: random.Random) -> bytes:
    op = rng.choice(OPS)
    n = rng.choice(
        ["18446744073709551616", "18446744073709551615", "01", "-0", "1.0", "1e2", "1E2", "00", "0", "100", "NaN",
         "Infinity", "-Infinity"]
    )  # fmt: skip
    commands = [
        {"cmd": "set", "value": 6},
        {"cmd": "apply", "op": op, "arg": 7},
        {"cmd": "get"},
    ]
    command = rng.choice(commands)
    compact = json.dumps(command, separators=(",", ":"))
    match rng.randrange(10):
        case 0:
            text = rng.choice(
                [
                    '{"cmd":"get","cmd":"get"}',
                    '{"cmd":"set","value":1,"value":2}',
                    '{"cmd":"set","value":1,"value":1}',
                    '{"cmd":"set","cmd":"apply","value":1}',
                    '{"cmd":"set","cmd":"set","value":1}',
                    f'{{"cmd":"apply","op":"{op}","op":"{op}","arg":1}}',
                    f'{{"cmd":"apply","op":"{op}","arg":1,"arg":2}}',
                    '{"cmd":"get","cmd":"set"}',
                ]
            )
        case 1:
            text = rng.choice(
                [
                    '{"value":6,"cmd":"set"}',
                    f'{{"arg":7,"op":"{op}","cmd":"apply"}}',
                    f'{{"op":"{op}","arg":7,"cmd":"apply"}}',
                    f'{{"op":"{op}","cmd":"apply","arg":7}}',
                    f'{{"arg":7,"cmd":"apply","op":"{op}"}}',
                    f'{{"cmd":"apply","arg":7,"op":"{op}"}}',
                ]
            )
        case 2:
            text = rng.choice(
                [
                    json.dumps(command),
                    json.dumps(command, indent=2),
                    json.dumps(command, indent="\t"),
                    json.dumps(command, indent=1).replace("\n", "\r\n"),
                    " \t\r\n" + compact + " \t\r\n",
                    compact.replace(":", " \t\r\n: \t\r\n"),
                    "\x0c" + compact,
                    compact + "\x0b",
                    "\u00a0" + compact,
                    compact.replace(",", ",\u2028"),
                ]
            )
        case 3 | 4:
            text = rng.choice([f'{{"cmd":"set","value":{n}}}', f'{{"cmd":"apply","op":"{op}","arg":{n}}}'])  # fmt: skip
        case 5:
            text = compact + rng.choice(
                ["{}", " 1", "]", ",", compact, " null", "\x00", '""']
            )
        case 6:
            text = rng.choice(
                [
                    "[" * 100 + compact + "]" * 100,
                    "[" * 100 + "]" * 100,
                    '{"cmd":' * 100 + '"get"' + "}" * 100,
                    '{"cmd":"set","value":' + "[" * 99 + "6" + "]" * 99 + "}",
                    '{"cmd":"get","x":' + "[" * 99 + "]" * 99 + "}",
                ]
            )
        case 7:
            text = rng.choice(
                [
                    '{"CMD":"get"}',
                    '{"Cmd":"get"}',
                    '{"cmd":"GET"}',
                    '{"cmd":"Get"}',
                    '{"cmd":"set","Value":6}',
                    '{"cmd":"set","VALUE":6}',
                    '{"cmd":"get","CMD":"get"}',
                    '{"cmd":"set","value":6,"Value":7}',
                    f'{{"cmd":"apply","OP":"{op}","arg":7}}',
                    f'{{"cmd":"apply","op":"{op.upper()}","arg":7}}',
                    f'{{"cmd":"apply","op":"{op}","Arg":7}}',
                ]
            )
        case 8:
            return compact.encode(
                rng.choice(["utf-16", "utf-16-le", "utf-16-be", "utf-32"])
            )
        case _:
            return rng.choice(
                [b"\xef\xbb\xbf" + compact.encode(), compact.encode() + b"\xef\xbb\xbf"]
            )
    return text.encode()


def request_line(rng: random.Random) -> str:
    exp = rng.choice([0, 1, 100, 2**64 - 1, rng.randrange(1000)])
    now = rng.choice(
        [0, exp, exp + 1 if exp < 2**64 - 1 else exp, rng.randrange(1000), exp, exp]
    )
    match rng.randrange(16):
        case 0:
            body = rng.choice(["xff", "toolarge", "unreadable"])
        case _:
            body = hexed(command_body(rng).encode())
            if COMPACT.randrange(4) == 0:
                body = hexed(compact_body(COMPACT).encode())
            if LIBRARY.randrange(5) == 0:
                body = hexed(library_body(LIBRARY))
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
