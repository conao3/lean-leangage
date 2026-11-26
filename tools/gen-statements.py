"""Writes the statement list that the Lean SQL oracle and the Rust, Python and Go shells all run.

Deterministic: the same seed and count give the same file. The line format is described in
`lean/SqlOracle.lean`.
"""

import random
import sys

NAMES = ["id", "body", "note", "tag", "a", 'x"y', '""', "é", "名前", "a b", "Tag"]
BAD_NAMES = ["", "tenant_id", "leangage_t", "n" * 64, "é" * 32, "a\x00b"]
KINDS = ["int", "bool", "text", "bytes"]
INTS = [0, 1, -1, 7, 2**31, -(2**63), 2**63 - 1]
TEXTS = ["", "a", '"', "'", "é", "名前", "a\x00b", "$1", "x'); DROP TABLE t; --"]


def hexed(s: str) -> str:
    return s.encode().hex()


def value_of(rng: random.Random, kind: str) -> str:
    if kind == "int":
        return f"i{rng.choice(INTS) if rng.randrange(2) else rng.randrange(-100, 100)}"
    if kind == "bool":
        return rng.choice(["b0", "b1"])
    if kind == "text":
        return "t" + hexed(rng.choice(TEXTS))
    return "y" + bytes(rng.randrange(256) for _ in range(rng.randrange(4))).hex()


def value(rng: random.Random, kind: str | None = None) -> str:
    """A value of the column's kind most of the time, else `NULL` or one of any kind."""
    roll = rng.randrange(10)
    if kind is not None and roll < 7:
        return value_of(rng, kind)
    if roll < 8:
        return "n"
    return value_of(rng, rng.choice(KINDS))


def schema(rng: random.Random) -> list[tuple[str, list[tuple[str, str, int]], int]]:
    """Up to 3 tables, valid unless one defect is put in."""
    names = rng.sample(NAMES, rng.randrange(1, 4))
    tables = []
    for n in names:
        cols = [
            (c, rng.choice(KINDS), rng.randrange(2))
            for c in rng.sample(NAMES, rng.randrange(1, 4))
        ]
        tables.append((n, cols, rng.randrange(len(cols) + 1)))
    if rng.randrange(5) == 0:
        t = rng.randrange(len(tables))
        n, cols, kl = tables[t]
        defect = rng.randrange(5)
        if defect == 0:
            tables[t] = (rng.choice(BAD_NAMES), cols, kl)
        elif defect == 1:
            cols = cols + [(rng.choice(BAD_NAMES), "int", 0)]
            tables[t] = (n, cols, kl)
        elif defect == 2:
            tables[t] = (n, cols + [cols[0]], kl)
        elif defect == 3:
            tables[t] = (n, cols, len(cols) + 1)
        else:
            tables[t] = (n, [], 0)
    return tables


def statement(rng: random.Random, tables: list) -> str:
    tenant = str(rng.choice(INTS) if rng.randrange(3) == 0 else rng.randrange(1, 4))
    ti = rng.randrange(len(tables)) if rng.randrange(8) else len(tables)
    _, cols, kl = tables[ti] if ti < len(tables) else ("", [], 0)
    kinds = [c[1] for c in cols]
    t = str(ti)

    def row(n: int) -> list[str]:
        if rng.randrange(8) == 0:
            n = rng.randrange(5)
        return [value(rng, kinds[i] if i < len(kinds) else None) for i in range(n)]

    def col() -> int:
        return (
            rng.randrange(len(cols)) if cols and rng.randrange(6) else rng.randrange(4)
        )

    kind = rng.randrange(5)
    if kind == 0:
        key_len = kl if rng.randrange(6) else rng.randrange(4)
        return " ".join(["put", tenant, t, str(key_len), *row(len(cols))])
    if kind == 1:
        return " ".join(["del", tenant, t, *row(kl)])
    if kind == 2:
        i = col()
        return " ".join(
            [
                "delwhere",
                tenant,
                t,
                str(i),
                value(rng, kinds[i] if i < len(kinds) else None),
            ]
        )
    if kind == 3:
        return f"select {tenant} {t}"
    i = col()
    return " ".join(
        ["select", tenant, t, str(i), value(rng, kinds[i] if i < len(kinds) else None)]
    )


def main() -> None:
    count = int(sys.argv[1])
    rng = random.Random(20261125)
    lines = 0
    while lines < count:
        tables = schema(rng)
        print("reset")
        for n, cols, kl in tables:
            print(
                " ".join(
                    [
                        "table",
                        hexed(n),
                        str(kl),
                        *(f"{hexed(c)}:{k}:{nl}" for c, k, nl in cols),
                    ]
                )
            )
        print("create")
        lines += len(tables) + 2
        for _ in range(30):
            print(statement(rng, tables))
            lines += 1


main()
