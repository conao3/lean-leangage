"""Fails unless the request path of the calculator's three servers and of the notes server calls
the generated functions.

For each file of the path it requires the calls of the functions generated from
`lean/Leangage/Http.lean`, `lean/Calculator/Wire.lean` and `lean/Notes/Wire.lean`, and refuses a
JSON library, a status code written in the file (a constant of the HTTP library or a number from
100 to 599) and the JSON writer called by hand. A test passes whichever code a handler runs; this check reads the
handlers.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).parent.parent

STATUS = (r"\b[1-5][0-9][0-9]\b", "a status code")

RUST = [
    (r"serde", "serde"),
    (r"StatusCode::[A-Z]", "a status constant"),
    (r"json_format", "the JSON writer"),
    STATUS,
]
PYTHON = [
    (r"\bjson\b", "json"),
    (r"HTTPStatus", "a status constant"),
    (r"json_format", "the JSON writer"),
    STATUS,
]
GO = [
    (r"encoding/json", "encoding/json"),
    (r"http\.Status", "a status constant"),
    (r"jsonformat", "the JSON writer"),
    STATUS,
]

# The file, what it must call, what it must not hold, and where the checked text ends.
FILES = [
    (
        "rust/leangage/src/http.rs",
        ["verifier.admit(", "A::request(", "A::respond(", "A::fingerprint(", "A::scope(", "http_format::failed("],
        RUST,
        None,
    ),
    (
        "rust/leangage/src/token.rs",
        ["http_format::authenticate(", "http_format::failed(Failure::BadSignature)"],
        RUST,
        "#[cfg(test)]",
    ),
    (
        "rust/calculator/src/lib.rs",
        ["wire::request(", "wire::respond(", "wire::fingerprint(", "wire::scope("],
        RUST,
        None,
    ),
    (
        "rust/notes/src/lib.rs",
        [
            "wire::request(", "wire::respond(", "wire::fingerprint(", "wire::scope(", "wire::encode_reply(",
            "wire::decode_reply(",
        ],
        RUST,
        None,
    ),
    (
        "python/src/leangage/http.py",
        ["verifier.admit(", "api.request(", "api.respond(", "api.fingerprint(", "api.scope(", "http_format.failed("],
        PYTHON,
        None,
    ),
    (
        "python/src/leangage/token.py",
        ["http_format.authenticate(", "http_format.failed(http_format.Failure.badSignature)"],
        PYTHON,
        None,
    ),
    (
        "python/src/leangage_calculator/__init__.py",
        ["request=wire.request", "respond=wire.respond", "fingerprint=wire.fingerprint", "scope=wire.scope"],
        PYTHON,
        None,
    ),
    (
        "go/leangage/http.go",
        ["verifier.Admit(", "api.Request(", "api.Respond(", "api.Fingerprint(", "api.Scope(", "httpformat.Failed("],
        GO,
        None,
    ),
    (
        "go/leangage/token.go",
        ["httpformat.Authenticate(", "httpformat.Failed(httpformat.FailureBadSignature())"],
        GO,
        None,
    ),
    (
        "go/calculator/calculator.go",
        ["wire.Request(", "wire.Respond(", "wire.Fingerprint(", "wire.Scope("],
        GO,
        None,
    ),
]  # fmt: skip


def main() -> None:
    problems = []
    for name, required, forbidden, end in FILES:
        text = (ROOT / name).read_text()
        if end is not None:
            text = text.split(end)[0]
        for call in required:
            if call not in text:
                problems.append(f"{name}: no call of {call}")
        for number, line in enumerate(text.splitlines(), 1):
            for pattern, what in forbidden:
                if re.search(pattern, line):
                    problems.append(f"{name}:{number}: {what}: {line.strip()}")
    for problem in problems:
        print(problem)
    if problems:
        sys.exit(1)
    print(f"{len(FILES)} files of the request path call the generated functions")


main()
