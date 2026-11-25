"""Writes the token list that the Lean token oracle and the Rust, Python and Go shells all run.

Deterministic: the same seed and count give the same file. The line format is described in
`lean/TokenOracle.lean`.
"""

import random
import sys

NUMBERS = [0, 1, 9, 10, 12, 99, 100, 10**19 - 1, 10**19, 2**63, 2**64 - 2, 2**64 - 1]
BAD_NUMBERS = [
    "",
    "00",
    "01",
    "007",
    "+1",
    "-1",
    "-0",
    " 1",
    "1 ",
    "1e3",
    "0x1",
    "١",
    str(2**64),
    str(10**20),
    "9" * 20,
    "0" * 21 + "1",
]
BYTES = b".0129:afgAFv1+- \x00\x7f\xc3\xa9\xff"


def number(rng: random.Random) -> int:
    return rng.choice(NUMBERS) if rng.randrange(2) else rng.randrange(1000)


def signature(rng: random.Random) -> bytes:
    return bytes(rng.randrange(256) for _ in range(rng.choice([0, 1, 2, 4, 32])))


def token(rng: random.Random) -> bytes:
    fields = (
        [b"v1"]
        + [str(number(rng)).encode() for _ in range(3)]
        + [signature(rng).hex().encode()]
    )
    if rng.randrange(4) == 0:
        fields[rng.randrange(1, 4)] = rng.choice(BAD_NUMBERS).encode()
    return b".".join(fields)


def edit(rng: random.Random, tok: bytes) -> bytes:
    i = rng.randrange(len(tok) + 1)
    c = bytes([rng.choice(BYTES)])
    match rng.randrange(8):
        case 0:
            return tok[:i] + c + tok[i + 1 :]
        case 1:
            return tok[:i] + c + tok[i:]
        case 2:
            return tok[:i] + tok[i + 1 :]
        case 3:
            return tok.upper()
        case 4:
            return rng.choice([b"v2", b"V1", b"v1.v1", b"", b"v"]) + tok[2:]
        case 5:
            return tok + rng.choice([b".", b".aa", b"a", b"0"])
        case 6:
            return tok.rsplit(b".", 1)[0]
        case _:
            return bytes(rng.choice(BYTES) for _ in range(rng.randrange(12)))


def main() -> None:
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    rng = random.Random(5415)
    for _ in range(count):
        match rng.randrange(3):
            case 0:
                t, u, e = number(rng), number(rng), number(rng)
                print(f"issue {t} {u} {e} x{signature(rng).hex()}")
            case 1:
                print(f"parse x{token(rng).hex()}")
            case _:
                print(f"parse x{edit(rng, token(rng)).hex()}")


main()
