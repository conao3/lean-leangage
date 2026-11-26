"""The generated Python JSON reader, the functions on requests and responses and the calculator's
functions on the wire against those run natively by Lean (`request-oracle`).

The line format is described in `lean/RequestOracle.lean`. A text to read that is UTF-8 is also
read by `readString`, which must read what `read` reads, and its acceptance is compared with that
of `json.loads`.
"""

import json
import os
import re
import subprocess
from pathlib import Path

from leanfran import Err, Ok
from leangage import http_format, json_read
from leangage_calculator import kernel, wire

CASES = Path(__file__).parents[2] / "testdata" / "request-cases.txt"

SURROGATE_ESCAPE = re.compile(r"\\u[dD][89a-fA-F]")
BODIES = {
    "notutf8": http_format.Body_notUtf8(),
    "toolarge": http_format.Body_tooLarge(),
    "unreadable": http_format.Body_unreadable(),
}
REFUSALS = {
    "overflow": kernel.Error.overflow,
    "underflow": kernel.Error.underflow,
    "division_by_zero": kernel.Error.divByZero,
}
FAILURES = {
    "bad_signature": http_format.Failure.badSignature,
    "conflict": http_format.Failure.conflict,
    "stopped": http_format.Failure.stopped,
    "retries_exhausted": http_format.Failure.retriesExhausted,
    "database": http_format.Failure.database,
    "commit_unknown": http_format.Failure.commitUnknown,
    "broken": http_format.Failure.broken,
}


def data(word: str) -> bytes:
    assert word.startswith("x"), word
    return bytes.fromhex(word[1:])


def show(value: bytes | list[int]) -> str:
    return "x" + bytes(value).hex()


def show_item(item: json_read.Item) -> str:
    match item:
        case json_read.Item_null():
            return "n"
        case json_read.Item_bool(b=b):
            return "t" if b else "f"
        case json_read.Item_num(n=n):
            return f"u{n}"
        case json_read.Item_number():
            return "#"
        case json_read.Item_str(s=s):
            return "s" + show(s)
        case json_read.Item_key(s=s):
            return "k" + show(s)
        case json_read.Item_arrOpen():
            return "["
        case json_read.Item_arrClose():
            return "]"
        case json_read.Item_objOpen():
            return "{"
        case json_read.Item_objClose():
            return "}"
    raise ValueError(item)


def show_response(head: str, r: http_format.Response) -> str:
    return f"{head} {r.status} {show(r.body)}"


def command(words: list[str]) -> kernel.Command:
    match words:
        case ["set", n]:
            return kernel.Command_set(value=int(n))
        case ["apply", op, n]:
            return kernel.Command_apply(op=kernel.Op(op), arg=int(n))
        case ["get"]:
            return kernel.Command_get()
    raise ValueError(words)


def show_command(cmd: kernel.Command) -> str:
    match cmd:
        case kernel.Command_set(value=value):
            return f"set {value}"
        case kernel.Command_apply(op=op, arg=arg):
            return f"apply {op.value} {arg}"
        case kernel.Command_get():
            return "get"
    raise ValueError(cmd)


def show_auth(result: Ok | Err) -> str:
    if isinstance(result, Err):
        return show_response("err", result.error)
    b = result.value
    return f"ok {b.tenant} {b.user} {b.exp} {show(b.payload)} {show(b.sig)}"


def accepted_by_json(text: str) -> bool:
    def refuse(name: str) -> None:
        raise ValueError(name)

    try:
        json.loads(text, parse_constant=refuse, parse_float=str, parse_int=str)
    except (ValueError, RecursionError):
        return False
    return True


class Counts:
    utf8 = 0
    compared = 0


def run(line: str, counts: Counts) -> str:
    match line.split(" "):
        case ["read", b]:
            raw = data(b)
            items = json_read.read(list(raw))
            try:
                text = raw.decode()
            except UnicodeDecodeError:
                text = None
            if text is not None:
                counts.utf8 += 1
                assert json_read.readString(text) == items, line
                if not SURROGATE_ESCAPE.search(text) and text.count("[") < 200:
                    counts.compared += 1
                    assert (items is not None) == accepted_by_json(text), line
            if items is None:
                return "none"
            return " ".join(["items"] + [show_item(i) for i in items])
        case ["auth", "-"]:
            return show_auth(http_format.authenticate(None))
        case ["auth", h]:
            return show_auth(http_format.authenticate(data(h).decode()))
        case ["request", tenant, user, exp, now, b]:
            body = BODIES.get(b) or http_format.Body_text(s=data(b).decode())
            result = wire.request(int(tenant), int(user), int(exp), int(now), body)
            if isinstance(result, Err):
                return show_response("err", result.error)
            call = result.value
            return f"ok {call.actor.org} {call.actor.user} {show_command(call.cmd)}"
        case ["respond", "ok", v]:
            return show_response("resp", wire.respond(Ok(value=kernel.Reply(v=int(v)))))
        case ["respond", "err", name]:
            return show_response("resp", wire.respond(Err(error=REFUSALS[name])))
        case ["failure", name]:
            return show_response("resp", http_format.failed(FAILURES[name]))
        case ["fingerprint", *cmd]:
            return "bytes " + show(wire.fingerprint(command(cmd)))
        case ["scope", user]:
            return "text " + show(
                wire.scope(kernel.Principal(org=0, user=int(user))).encode()
            )
    raise ValueError(line)


def test_generated_python_request_functions_agree_with_lean() -> None:
    text_in = CASES.read_text()
    oracle = subprocess.run(
        [os.environ["LEANGAGE_REQUEST_ORACLE"]],
        input=text_in,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    counts = Counts()
    ours = [run(line, counts) for line in text_in.splitlines()]
    assert counts.utf8 > 800
    assert counts.compared > 700
    assert ours == oracle.splitlines()
