"""Writes the command list that the Lean oracle, the Rust shell and the Python shell all run.

Deterministic: the same seed and count give the same file.
"""

import random
import sys

EDGES = [0, 1, 2, 3, 7, 2**32, 2**63 - 1, 2**63, 2**64 - 2, 2**64 - 1]


def number(rng: random.Random) -> int:
    kind = rng.randrange(4)
    if kind == 0:
        return rng.choice(EDGES)
    if kind == 1:
        return rng.randrange(2**64)
    return rng.randrange(100)


def main() -> None:
    count = int(sys.argv[1])
    rng = random.Random(20261124)
    for _ in range(count):
        who = f"{rng.randrange(1, 4)} {rng.randrange(1, 6)}"
        kind = rng.randrange(10)
        if kind < 3:
            print(f"{who} set {number(rng)}")
        elif kind < 8:
            op = rng.choice(["add", "sub", "mul", "div"])
            print(f"{who} apply {op} {number(rng)}")
        else:
            print(f"{who} get")


main()
