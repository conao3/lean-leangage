"""The generated Python JSON writer against the one run natively by Lean (`json-oracle`).

The line format is described in `lean/JsonOracle.lean`. A list whose strings are UTF-8 is also
written by `writeArray`, which must write what `write` writes.
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


STR_FIXED = {
    "n": json_format.StrTok_null(),
    "t": json_format.StrTok_bool(b=True),
    "f": json_format.StrTok_bool(b=False),
    "[": json_format.StrTok_arrOpen(),
    "]": json_format.StrTok_arrClose(),
    "{": json_format.StrTok_objOpen(),
    "}": json_format.StrTok_objClose(),
}


def str_tok(word: str) -> json_format.StrTok:
    """The token with strings; raises `UnicodeDecodeError` for a string that is not UTF-8."""
    if word in STR_FIXED:
        return STR_FIXED[word]
    if word.startswith("u"):
        return json_format.StrTok_num(n=int(word[1:]))
    if word.startswith("sx"):
        return json_format.StrTok_str(s=bytes.fromhex(word[2:]).decode())
    if word.startswith("kx"):
        return json_format.StrTok_key(s=bytes.fromhex(word[2:]).decode())
    raise ValueError(word)


def str_toks(words: list[str]) -> list[json_format.StrTok] | None:
    try:
        return [str_tok(w) for w in words]
    except UnicodeDecodeError:
        return None


def run(line: str) -> str:
    head, *words = line.split(" ")
    assert head == "write", line
    written = bytes(json_format.write([tok(w) for w in words]))
    toks = str_toks(words)
    if toks is not None:
        assert bytes(json_format.writeArray(toks)) == written, line
    return "json x" + written.hex()


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
    assert (
        sum(str_toks(line.split(" ")[1:]) is not None for line in text_in.splitlines())
        > 1000
    )
    assert ours == oracle.splitlines()
