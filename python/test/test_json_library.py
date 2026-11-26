"""What `leangage.json_text.tokens` gives for the texts on which the JSON libraries of the three
servers differ, and for those each must refuse.

Each case is a name, the bytes of a body and the tokens in the format of
`lean/RequestOracle.lean`, or `None` for a body `json` refuses.
"""

import pytest
from leangage import json_lexemes
from leangage.json_text import tokens
from test_request_differential import show_token

CASES: list[tuple[str, bytes, str | None]] = [
    ("lone high surrogate", b'"\\ud800"', None),
    ("lone low surrogate", b'"\\udc00"', None),
    ("surrogate pair", b'"\\ud83d\\ude00"', "sxf09f9880"),
    ("depth 200", b"[" * 200 + b"]" * 200, " ".join(["["] * 200 + ["]"] * 200)),
    ("depth 2000", b"[" * 2000 + b"]" * 2000, " ".join(["["] * 2000 + ["]"] * 2000)),
    ("depth 200000", b"[" * 200_000 + b"]" * 200_000, None),
    ("NaN", b"NaN", None),
    ("Infinity", b"Infinity", None),
    ("-Infinity", b"-Infinity", None),
    ("exponent 400", b"1e400", "#"),
    ("minus zero", b"-0", "#"),
    ("fraction", b"1.0", "#"),
    ("exponent", b"1e2", "#"),
    ("2^64 - 1", b"18446744073709551615", "u18446744073709551615"),
    ("2^64", b"18446744073709551616", "#"),
    ("leading zero", b"01", None),
    ("5000 digits", b"7" * 5000, "#"),
    ("two objects", b"{} {}", None),
    ("two numbers", b"1 2", None),
    ("one more bracket", b"[]]", None),
    ("member twice", b'{"a":1,"a":2}', "{ kx61 u1 kx61 u2 }"),
    ("upper-case key", b'{"CMD":"get"}', "{ kx434d44 sx676574 }"),
    ("byte order mark", b"\xef\xbb\xbf{}", None),
    ("UTF-16", "{}".encode("utf-16-le"), None),
    ("UTF-16 with a byte order mark", "{}".encode("utf-16"), None),
    ("byte that is not UTF-8 in a string", b'"\xff"', None),
    ("control character in a string", b'"\x01"', None),
    ("empty", b"", None),
    ("spaces only", b" \n", None),
    ("spaces around", b' \t\r\n{"a" : [ null , true ] }\n', "{ kx61 [ n t ] }"),
]


@pytest.mark.parametrize(("name", "body", "want"), CASES, ids=[c[0] for c in CASES])
def test_json_library(name: str, body: bytes, want: str | None) -> None:
    read = tokens(body)
    got = None
    if read is not None:
        got = " ".join(show_token(t) for t in json_lexemes.unpack(read))
    assert got == want
