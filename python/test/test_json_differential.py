"""The generated Python JSON writer against the one run natively by Lean (`json-oracle`).

The line format is described in `lean/JsonOracle.lean`.
"""

import os
import subprocess
from pathlib import Path

from leanharbor import json_format

CASES = Path(__file__).parents[2] / "testdata" / "json-cases.txt"

FIXED = {
    "n": json_format.Tok_null(),
    "t": json_format.Tok_bool(b=True),
    "f": json_format.Tok_bool(b=False),
    "[": json_format.Tok_arrOpen(),
    "]": json_format.Tok_arrClose(),
    "{": json_format.Tok_objOpen(),
    "}": json_format.Tok_objClose(),
}


def tok(word: str) -> json_format.Tok:
    if word in FIXED:
        return FIXED[word]
    if word.startswith("u"):
        return json_format.Tok_num(n=int(word[1:]))
    if word.startswith("sx"):
        return json_format.Tok_str(s=list(bytes.fromhex(word[2:])))
    if word.startswith("kx"):
        return json_format.Tok_key(s=list(bytes.fromhex(word[2:])))
    raise ValueError(word)


def run(line: str) -> str:
    head, *words = line.split(" ")
    assert head == "write", line
    return "json x" + bytes(json_format.write([tok(w) for w in words])).hex()


def test_generated_python_json_writer_agrees_with_lean() -> None:
    text_in = CASES.read_text()
    oracle = subprocess.run(
        [os.environ["LEANHARBOR_JSON_ORACLE"]],
        input=text_in,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    ours = [run(line) for line in text_in.splitlines()]
    assert ours == oracle.splitlines()
