"""Writes the notes command list that the Lean oracle and the Rust, Python and Go servers all run.

Deterministic: the same seed and count give the same file. Each org starts with an admin. Bodies have no space; some are empty,
and some sit at the 4096-byte limit with characters of 1 to 4 bytes in UTF-8.
"""

import random
import sys

ALPHABET = list(
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_.,!?#"
) + [
    "é",
    "ß",
    "あ",
    "日",
    "本",
    "😀",
    "🎉",
]

EDGES = [
    "a" * 4096,
    "a" * 4097,
    "a" * 4095 + "é",
    "a" * 4094 + "é",
    "😀" * 1024,
    "😀" * 1025,
    "あ" * 1365 + "a",
    "あ" * 1366,
]


def body(rng: random.Random) -> str:
    kind = rng.randrange(100)
    if kind < 8:
        return ""
    if kind < 10:
        return rng.choice(EDGES)
    return "".join(rng.choice(ALPHABET) for _ in range(rng.randrange(1, 13)))


def flag(rng: random.Random, chance: float) -> str:
    return "1" if rng.random() < chance else "0"


def main() -> None:
    count = int(sys.argv[1])
    rng = random.Random(20261125)
    print("1 1 add-member 1 1")
    print("2 3 add-member 3 1")
    for _ in range(count - 2):
        who = f"{rng.randrange(1, 3)} {rng.randrange(1, 6)}"
        kind = rng.randrange(100)
        if kind < 15:
            print(f"{who} add-member {rng.randrange(1, 7)} {flag(rng, 0.5)}")
        elif kind < 20:
            print(f"{who} remove-member {rng.randrange(1, 7)}")
        elif kind < 55:
            print(f"{who} put-note {rng.randrange(12)} {flag(rng, 0.4)} {body(rng)}")
        elif kind < 65:
            print(f"{who} delete-note {rng.randrange(12)}")
        elif kind < 80:
            print(f"{who} read-note {rng.randrange(12)}")
        elif kind < 90:
            print(f"{who} list-notes")
        else:
            print(f"{who} list-members")


main()
