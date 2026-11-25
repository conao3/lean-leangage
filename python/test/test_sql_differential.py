"""The generated Python SQL compiler against the one run natively by Lean (`sql-oracle`).

The line format is described in `lean/SqlOracle.lean`.
"""

import os
import subprocess
from pathlib import Path

from leanharbor import sql

STATEMENTS = Path(__file__).parents[2] / "testdata" / "sql-statements.txt"


def text(s: str) -> str:
    return bytes.fromhex(s).decode()


def value(s: str) -> sql.Val:
    match s[0], s[1:]:
        case "i", v:
            return sql.Val_int(v=int(v))
        case "b", "0":
            return sql.Val_bool(v=False)
        case "b", "1":
            return sql.Val_bool(v=True)
        case "t", v:
            return sql.Val_text(v=text(v))
        case "y", v:
            return sql.Val_bytes(v=list(bytes.fromhex(v)))
        case "n", "":
            return sql.Val_null()
    raise ValueError(s)


def show_value(v: sql.Val) -> str:
    match v:
        case sql.Val_int(v=n):
            return f"i{n}"
        case sql.Val_bool(v=b):
            return f"b{int(b)}"
        case sql.Val_text(v=t):
            return "t" + t.encode().hex()
        case sql.Val_bytes(v=bs):
            return "y" + bytes(bs).hex()
        case sql.Val_null():
            return "n"
    raise ValueError(v)


def column(s: str) -> sql.Col:
    name, kind, nullable = s.split(":")
    return sql.Col(name=text(name), kind=sql.Kind(kind), nullable=nullable == "1")


def show(compiled: tuple[sql.Sql, list[sql.Val]] | None) -> str:
    if compiled is None:
        return "none"
    q, ps = compiled
    return " ".join(["sql", sql.render(q).encode().hex(), *map(show_value, ps)])


def run(schema: list[sql.Tab], line: str) -> str:
    match line.split(" "):
        case ["reset"]:
            schema.clear()
            return "ok"
        case ["table", name, kl, *cols]:
            schema.append(
                sql.Tab(name=text(name), cols=[column(c) for c in cols], kl=int(kl))
            )
            return f"valid {str(sql.valid(schema)).lower()}"
        case ["create"]:
            return " ".join(
                ["create", *(sql.render(sql.create(t)).encode().hex() for t in schema)]
            )
        case ["put", tv, t, kl, *vs]:
            w = sql.Write_put(table=int(t), keyLen=int(kl), row=[value(v) for v in vs])
            return show(sql.compile(schema, int(tv), sql.plan(w)))
        case ["del", tv, t, *vs]:
            w = sql.Write_del_(table=int(t), key=[value(v) for v in vs])
            return show(sql.compile(schema, int(tv), sql.plan(w)))
        case ["delwhere", tv, t, i, v]:
            w = sql.Write_delWhere(table=int(t), col=int(i), val=value(v))
            return show(sql.compile(schema, int(tv), sql.plan(w)))
        case ["select", tv, t]:
            return show(sql.select(schema, int(tv), int(t), None))
        case ["select", tv, t, i, v]:
            return show(sql.select(schema, int(tv), int(t), (int(i), value(v))))
    raise ValueError(line)


def test_generated_python_sql_agrees_with_lean() -> None:
    text_in = STATEMENTS.read_text()
    oracle = subprocess.run(
        [os.environ["LEANHARBOR_SQL_ORACLE"]],
        input=text_in,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    schema: list[sql.Tab] = []
    ours = [run(schema, line) for line in text_in.splitlines()]
    assert sum(line.startswith("sql ") for line in ours) > 100
    assert ours == oracle.splitlines()
