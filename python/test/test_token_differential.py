"""The generated Python token functions against the ones run natively by Lean (`token-oracle`).

The line format is described in `lean/TokenOracle.lean`.
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


def run(line: str) -> str:
    match line.split(" "):
        case ["parse", tok]:
            p = token_format.parse(data(tok))
            if p is None:
                return "none"
            return f"parsed {p.tenant} {p.user} {p.exp} {show(p.payload)} {show(p.sig)}"
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
    assert ours == oracle.splitlines()
