"""Writes the token lists that the Lean JSON oracle and the Rust, Python and Go shells all write.

Deterministic: the same seed and count give the same file. The line format is described in
`lean/JsonOracle.lean`. Strings hold control bytes, quotes, backslashes, bytes of UTF-8 and bytes
that are not UTF-8; half of the lists are JSON documents and the other half any tokens.
"""

import random
import sys

NUMBERS = [0, 1, 9, 10, 99, 100, 10**19 - 1, 10**19, 2**63, 2**64 - 1]
SPECIAL = b'\x00\x01\x08\t\n\x0c\r\x1f\x1e "\\/:,[]{}u\x7f'
UTF8 = ["é", "日本", "😀", " ", "﻿"]


def string(rng: random.Random) -> bytes:
    out = b""
    for _ in range(rng.randrange(8)):
        match rng.randrange(5):
            case 0:
                out += bytes([rng.choice(SPECIAL)])
            case 1:
                out += rng.choice(UTF8).encode()
            case 2:
                out += bytes([rng.randrange(256)])
            case _:
                out += bytes([rng.randrange(32, 127)])
    return out


def number(rng: random.Random) -> int:
    return rng.choice(NUMBERS) if rng.randrange(2) else rng.randrange(1000)


def scalar(rng: random.Random) -> list[str]:
    match rng.randrange(5):
        case 0:
            return ["n"]
        case 1:
            return [rng.choice(["t", "f"])]
        case 2:
            return [f"u{number(rng)}"]
        case _:
            return [f"sx{string(rng).hex()}"]


def value(rng: random.Random, depth: int) -> list[str]:
    if depth == 0 or rng.randrange(3) == 0:
        return scalar(rng)
    n = rng.randrange(4)
    if rng.randrange(2):
        return ["["] + [t for _ in range(n) for t in value(rng, depth - 1)] + ["]"]
    members = [
        t for _ in range(n) for t in [f"kx{string(rng).hex()}"] + value(rng, depth - 1)
    ]
    return ["{"] + members + ["}"]


def any_tokens(rng: random.Random) -> list[str]:
    kinds = ["n", "t", "f", "[", "]", "{", "}"]
    out = []
    for _ in range(rng.randrange(8)):
        match rng.randrange(4):
            case 0:
                out.append(f"u{number(rng)}")
            case 1:
                out.append(f"{rng.choice('sk')}x{string(rng).hex()}")
            case _:
                out.append(rng.choice(kinds))
    return out


def main() -> None:
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    rng = random.Random(5417)
    for _ in range(count):
        toks = value(rng, 3) if rng.randrange(2) else any_tokens(rng)
        print(" ".join(["write"] + toks))


main()
