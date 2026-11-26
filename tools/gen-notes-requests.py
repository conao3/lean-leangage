"""Writes the lines that the Lean notes request oracle and the Rust notes server both answer.

Deterministic: the same seed and count give the same file. The line format is described in
`lean/NotesRequestOracle.lean`. The bodies are the notes' commands with their members in any
order and with every spelling of a string, and bodies close to one: a member removed, added,
repeated or holding another value. `library_body` writes the bodies on which a JSON library could
differ from the grammar: a member twice, members in another order, the space between tokens,
numbers at 2^64, data after the value, arrays nested 100 deep, `NaN` and `Infinity`, member names
in upper case, UTF-16 and a byte order mark. The stored replies are the bodies of the replies and texts
close to one.
"""

import json
import random
import sys

NUMBERS = [0, 1, 9, 10, 99, 100, 10**19 - 1, 10**19, 2**63, 2**64 - 1]
SPELLINGS = ["-0", "-1", "6.0", "1e3", "18446744073709551616", "null", '"6"', "[6]", '{"n":6}', "true", '""']  # fmt: skip
SPACE = ["", "", "", " ", "\n", "\t", "\r", "  ", " \n "]
TEXTS = [
    "", "a", "draft", "for everyone", "ノート", "é", "😀", 'say "hi"', "back\\slash", "line\nbreak",
    "tab\there", "\r", "\x08\x0c", "\x00", "a\x00b", "\x01\x1f", "\x7f", "/", "{}", "[1,2]", "'",
    "a" * 300, "あ" * 40, "́", "\u200b", " ", "﻿", "\U000e0001",
]  # fmt: skip
ESCAPED = [
    '"\\u0041"', '"\\u00e9"', '"\\ud83d\\ude00"', '"\\/"', '"\\b\\f\\n\\r\\t"', '"\\u0000"',
    '"a\\u0020b"',
]  # fmt: skip
REFUSALS = ["denied", "not_found", "bad_text"]
LIBRARY = random.Random(2647)


def hexed(data: bytes) -> str:
    return "x" + data.hex()


def number(rng: random.Random) -> int:
    return rng.choice(NUMBERS) if rng.randrange(2) else rng.randrange(1000)


def flag(rng: random.Random) -> str:
    return rng.choice(["t", "f"])


def text(rng: random.Random) -> str:
    return rng.choice(TEXTS)


def operand(rng: random.Random) -> str:
    if rng.randrange(8) == 0:
        return rng.choice(SPELLINGS)
    return str(number(rng))


def boolean(rng: random.Random) -> str:
    if rng.randrange(8) == 0:
        return rng.choice(["null", "1", "0", '"true"', "[true]", "tru"])
    return rng.choice(["true", "false"])


def string(rng: random.Random) -> str:
    match rng.randrange(10):
        case 0:
            return rng.choice(ESCAPED)
        case 1:
            return rng.choice(["null", "7", "true", '["a"]', '{"a":"b"}'])
        case 2:
            return json.dumps(text(rng))
        case _:
            return json.dumps(text(rng), ensure_ascii=False)


def spelled(rng: random.Random, members: list[tuple[str, str]]) -> str:
    def ws() -> str:
        return rng.choice(SPACE)

    rng.shuffle(members)
    inner = ",".join(f"{ws()}{json.dumps(k)}{ws()}:{ws()}{v}{ws()}" for k, v in members)
    return ws() + "{" + (inner or ws()) + "}" + ws()


def command_members(rng: random.Random) -> list[tuple[str, str]]:
    match rng.randrange(9):
        case 0:
            return [
                ("cmd", '"add_member"'),
                ("user", operand(rng)),
                ("admin", boolean(rng)),
            ]
        case 1:
            return [("cmd", '"remove_member"'), ("user", operand(rng))]
        case 2 | 3 | 4:
            return [
                ("cmd", '"put_note"'),
                ("id", operand(rng)),
                ("body", string(rng)),
                ("shared", boolean(rng)),
            ]
        case 5:
            return [("cmd", '"delete_note"'), ("id", operand(rng))]
        case 6:
            return [("cmd", '"read_note"'), ("id", operand(rng))]
        case 7:
            return [("cmd", '"list_notes"')]
        case _:
            return [("cmd", '"list_members"')]


def command_body(rng: random.Random) -> str:
    members = command_members(rng)
    match rng.randrange(14):
        case 0:
            members.append(
                rng.choice(
                    [
                        ("id", "6"),
                        ("user", "1"),
                        ("body", '"x"'),
                        ("x", "null"),
                        ("cmd", '"list_notes"'),
                        ("shared", "true"),
                        ("admin", "false"),
                    ]
                )
            )
        case 1:
            members.pop(rng.randrange(len(members)))
        case 2:
            k, v = members[0]
            members[0] = (rng.choice([k.upper(), k + " ", "c\\u006dd"]), v)
        case 3:
            members = [
                (
                    k,
                    rng.choice(
                        ['"put"', '"Put_Note"', '"list_note"', "null", "1", '"list_note\\u0073"', '"read_note"']
                    )
                    if k == "cmd"
                    else v,
                )
                for k, v in members
            ]  # fmt: skip
        case 4:
            return rng.choice(
                ["[]", "null", '"list_notes"', "7", '{"cmd":"list_notes"} x', "{", "", '[{"cmd":"list_notes"}]', "{}"]
            )  # fmt: skip
    body = spelled(rng, members)
    if rng.randrange(20) == 0:
        return body.replace('"cmd"', '"\\u0063md"')
    return body


def library_body(rng: random.Random) -> bytes:
    n = rng.choice(
        ["18446744073709551616", "18446744073709551615", "01", "-0", "1.0", "1e2", "1E2", "00", "0", "NaN", "Infinity"]
    )  # fmt: skip
    command = rng.choice(
        [
            {"cmd": "add_member", "user": 2, "admin": False},
            {"cmd": "remove_member", "user": 2},
            {"cmd": "put_note", "id": 7, "body": "text", "shared": True},
            {"cmd": "delete_note", "id": 7},
            {"cmd": "read_note", "id": 7},
            {"cmd": "list_notes"},
            {"cmd": "list_members"},
        ]
    )
    compact = json.dumps(command, separators=(",", ":"))
    members = [(json.dumps(k), json.dumps(v)) for k, v in command.items()]
    match rng.randrange(9):
        case 0:
            k, v = rng.choice(members)
            text = "{" + ",".join(f"{a}:{b}" for a, b in [*members, (k, v)]) + "}"
        case 1:
            text = "{" + ",".join(f"{a}:{b}" for a, b in reversed(members)) + "}"
        case 2:
            text = rng.choice(
                [
                    json.dumps(command),
                    json.dumps(command, indent=2),
                    json.dumps(command, indent="\t"),
                    " \t\r\n" + compact + " \t\r\n",
                    "\x0c" + compact,
                    "\u00a0" + compact,
                ]
            )
        case 3:
            text = rng.choice(
                [f'{{"cmd":"read_note","id":{n}}}', f'{{"cmd":"remove_member","user":{n}}}', f'{{"cmd":"delete_note","id":{n}}}']
            )  # fmt: skip
        case 4:
            text = compact + rng.choice(["{}", " 1", "]", ",", compact, " null"])
        case 5:
            text = rng.choice(
                [
                    "[" * 100 + compact + "]" * 100,
                    '{"cmd":' * 100 + '"list_notes"' + "}" * 100,
                    '{"cmd":"list_notes","x":' + "[" * 99 + "]" * 99 + "}",
                ]
            )
        case 6:
            k, v = members[-1]
            text = (
                "{"
                + ",".join(f"{a}:{b}" for a, b in [*members[:-1], (k.upper(), v)])
                + "}"
            )
        case 7:
            return compact.encode(rng.choice(["utf-16", "utf-16-le", "utf-16-be"]))
        case _:
            return b"\xef\xbb\xbf" + compact.encode()
    return text.encode()


def request_line(rng: random.Random) -> str:
    exp = rng.choice([0, 1, 100, 2**64 - 1, rng.randrange(1000)])
    now = rng.choice(
        [0, exp, exp + 1 if exp < 2**64 - 1 else exp, rng.randrange(1000), exp, exp]
    )
    if rng.randrange(16) == 0:
        body = rng.choice(["xff", "toolarge", "unreadable"])
    else:
        body = hexed(command_body(rng).encode())
        if LIBRARY.randrange(6) == 0:
            body = hexed(library_body(LIBRARY))
    return f"request {number(rng)} {number(rng)} {exp} {now} {body}"


def command(rng: random.Random) -> str:
    match rng.randrange(9):
        case 0:
            return f"add_member {number(rng)} {flag(rng)}"
        case 1:
            return f"remove_member {number(rng)}"
        case 2 | 3 | 4:
            return f"put_note {number(rng)} {flag(rng)} {hexed(text(rng).encode())}"
        case 5:
            return f"delete_note {number(rng)}"
        case 6:
            return f"read_note {number(rng)}"
        case 7:
            return "list_notes"
        case _:
            return "list_members"


def note(rng: random.Random) -> tuple[int, int, bool, str]:
    return (number(rng), number(rng), rng.randrange(2) == 0, text(rng))


def member(rng: random.Random) -> tuple[int, bool]:
    return (number(rng), rng.randrange(2) == 0)


def show_flag(b: bool) -> str:
    return "t" if b else "f"


def show_note(n: tuple[int, int, bool, str]) -> str:
    return f"{n[0]}:{n[1]}:{show_flag(n[2])}:{hexed(n[3].encode())}"


def reply(rng: random.Random) -> tuple[str, object]:
    """A reply as a line holds it, and the JSON value of its body."""

    def note_value(n: tuple[int, int, bool, str]) -> dict[str, object]:
        return {"body": n[3], "id": n[0], "owner": n[1], "shared": n[2]}

    match rng.randrange(4):
        case 0:
            return "done", {"done": True}
        case 1:
            n = note(rng)
            return f"found {show_note(n)}", {"note": note_value(n)}
        case 2:
            ns = [note(rng) for _ in range(rng.randrange(4))]
            return " ".join(["notes", *map(show_note, ns)]), {
                "notes": [note_value(n) for n in ns]
            }
        case _:
            ms = [member(rng) for _ in range(rng.randrange(4))]
            return " ".join(["members", *(f"{m[0]}:{show_flag(m[1])}" for m in ms)]), {
                "members": [{"admin": m[1], "user": m[0]} for m in ms]
            }


def edited(rng: random.Random, data: bytes) -> bytes:
    if not data:
        return b" "
    i = rng.randrange(len(data))
    c = bytes([rng.choice(b'"\\,:[]{}0123456789tfn abdeimnorsuy')])
    match rng.randrange(4):
        case 0:
            return data[:i] + data[i + 1 :]
        case 1:
            return data[:i] + c + data[i:]
        case 2:
            return data[:i] + c + data[i + 1 :]
        case _:
            return data[:i]


def stored_line(rng: random.Random) -> str:
    _, value = reply(rng)
    match rng.randrange(8):
        case 0:
            body = json.dumps(value).encode()
        case 1:
            body = json.dumps(value, separators=(",", ":")).encode()
            body = edited(rng, body).decode(errors="replace").encode()
        case 2:
            body = rng.choice(
                [
                    '{"done":false}',
                    '{"done":true,"done":true}',
                    '{"note":{"id":1,"owner":2,"shared":true,"body":"a"}}',
                    '{"note":{"body":"a","id":1,"owner":2,"shared":true,"x":1}}',
                    '{"notes":[{"body":"a","id":1,"owner":2}]}',
                    '{"members":[{"user":1,"admin":true}]}',
                    '{"members":[{"admin":true,"user":1},{"admin":1,"user":1}]}',
                    '{"members":{"admin":true,"user":1}}',
                    '{"notes":[[]]}',
                    '{"error":"denied"}',
                    "{}",
                    "[]",
                    "",
                ]
            ).encode()
        case _:
            body = json.dumps(value, separators=(",", ":"), ensure_ascii=False).encode()
    return f"stored {hexed(body)}"


def other_line(rng: random.Random) -> str:
    match rng.randrange(10):
        case 0 | 1 | 2:
            return f"respond ok {reply(rng)[0]}"
        case 3:
            return f"respond err {rng.choice(REFUSALS)}"
        case 4:
            return f"scope {number(rng)}"
        case 5 | 6:
            return stored_line(rng)
        case _:
            return f"fingerprint {command(rng)}"


def main() -> None:
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    rng = random.Random(7311)
    for _ in range(count):
        if rng.randrange(20) < 12:
            print(request_line(rng))
        else:
            print(other_line(rng))


main()
