"""The generated Python token functions against the ones run natively by Lean (`token-oracle`).

The line format is described in `lean/TokenOracle.lean`. A token that is UTF-8 is also split by
`parseString`, which must give what `parse` gives.
"""

import os
import subprocess
from pathlib import Path

from leanharbor import token_format

CASES = Path(__file__).parents[2] / "testdata" / "token-cases.txt"


def data(s: str) -> list[int]:
    assert s.startswith("x")
    return list(bytes.fromhex(s[1:]))


def show(bs: list[int]) -> str:
    return "x" + bytes(bs).hex()


def parsed(p: token_format.Parsed | token_format.ParsedArray | None) -> str:
    if p is None:
        return "none"
    return f"parsed {p.tenant} {p.user} {p.exp} {show(p.payload)} {show(p.sig)}"


def utf8(bs: list[int]) -> str | None:
    try:
        return bytes(bs).decode()
    except UnicodeDecodeError:
        return None


def run(line: str) -> str:
    match line.split(" "):
        case ["parse", tok]:
            out = parsed(token_format.parse(data(tok)))
            text = utf8(data(tok))
            if text is not None:
                assert parsed(token_format.parseString(text)) == out, text
            return out
        case ["issue", t, u, e, sig]:
            payload = token_format.encodePayload(int(t), int(u), int(e))
            return "token " + show(token_format.join(payload, data(sig)))
    raise ValueError(line)


def test_generated_python_token_functions_agree_with_lean() -> None:
    text_in = CASES.read_text()
    oracle = subprocess.run(
        [os.environ["LEANHARBOR_TOKEN_ORACLE"]],
        input=text_in,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    ours = [run(line) for line in text_in.splitlines()]
    assert sum(line.startswith("parsed ") for line in ours) > 100
    assert sum(line == "none" for line in ours) > 100
    tokens = [
        line.split(" ")[1] for line in text_in.splitlines() if line.startswith("parse ")
    ]
    assert sum(utf8(data(tok)) is not None for tok in tokens) > 1000
    assert ours == oracle.splitlines()
