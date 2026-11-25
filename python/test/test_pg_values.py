"""Every kind of `Val`, `NULL` included, written by the engine and read back unchanged, in a table
whose name holds `"`, a space and a letter outside ASCII. A text holding NUL, which PostgreSQL
cannot store, fails the command instead of storing something else, and the generated `compile`
refuses a value of another kind than its column's. A tenant id of 2^63 or more is stored as the
`Int64` with the same bits."""

from dataclasses import dataclass

import pytest
from leanharbor import Broken, DatabaseError, Kernel, Storage, sql
from leanharbor.pg import PgEngine
from leanharbor.pg.testing import cluster, connect

Row = list[sql.Val]


@dataclass(frozen=True)
class Put:
    row: Row


@dataclass(frozen=True)
class Read:
    pass


def _transition(
    _: int, snap: list[Row], cmd: Put | Read
) -> tuple[list[Row], list[Row]]:
    """Rows of one table, stored as the commands give them."""
    match cmd:
        case Put(row):
            return [row], []
        case Read():
            return [], snap


ROWS = Storage(
    kernel=Kernel(
        init=list,
        tenant=lambda actor: actor,
        transition=_transition,
        apply=lambda snap, _: snap,
        read_only=lambda cmd: isinstance(cmd, Read),
    ),
    tables=lambda: [
        sql.Tab(
            name='odd "näme"',
            cols=[
                sql.Col(name="k", kind=sql.Kind.int, nullable=False),
                sql.Col(name="b", kind=sql.Kind.bool, nullable=True),
                sql.Col(name='t "x"', kind=sql.Kind.text, nullable=True),
                sql.Col(name="y", kind=sql.Kind.bytes, nullable=True),
                sql.Col(name="i", kind=sql.Kind.int, nullable=True),
            ],
            kl=1,
        )
    ],
    load=lambda rows: rows[0] if len(rows) == 1 else None,
    writes=lambda ws: [sql.Write_put(table=0, keyLen=1, row=row) for row in ws],
    encode_reply=lambda _: b"",
    decode_reply=lambda _: None,
)

MIN, MAX = -(2**63), 2**63 - 1


def int_(v: int) -> sql.Val:
    return sql.Val_int(v=v)


NULL = sql.Val_null()


def key(row: Row) -> int:
    k = row[0]
    assert isinstance(k, sql.Val_int)
    return k.v


def test_every_kind_reads_back_as_written() -> None:
    url = cluster().locked(ROWS, "values_kinds")
    pg = PgEngine.connect(ROWS, url, 2)
    rows = [
        [
            int_(MIN),
            sql.Val_bool(v=True),
            sql.Val_text(v=""),
            sql.Val_bytes(v=[]),
            int_(MAX),
        ],
        [
            int_(-1),
            sql.Val_bool(v=False),
            sql.Val_text(v="\"quoted\" 'single' \\ é 日本 🦀 \x7f %s $1"),
            sql.Val_bytes(v=list(range(256))),
            int_(0),
        ],
        [int_(0), NULL, NULL, NULL, NULL],
        [
            int_(MAX),
            sql.Val_bool(v=True),
            sql.Val_text(v="x" * 10_000),
            sql.Val_bytes(v=[0]),
            NULL,
        ],
    ]
    for row in rows:
        assert pg.execute(1, Put(row)) == []
    replaced = [int_(-1), NULL, sql.Val_text(v="new"), NULL, int_(7)]
    pg.execute(1, Put(replaced))
    expected = list(rows)
    expected[1] = replaced
    read = pg.execute(1, Read())
    assert sorted(read, key=key) == sorted(expected, key=key)
    assert pg.execute(2, Read()) == [], "another tenant"

    nul = [int_(5), NULL, sql.Val_text(v="a\0b"), NULL, NULL]
    with pytest.raises(DatabaseError):
        pg.execute(1, Put(nul))
    other_kind = [int_(6), NULL, NULL, NULL, sql.Val_text(v="7")]
    with pytest.raises(Broken, match="a write does not compile"):
        pg.execute(1, Put(other_kind))
    assert len(pg.execute(1, Read())) == 4, "nothing stored"


def test_tenants_of_the_upper_half_keep_their_bits() -> None:
    name = "values_tenants"
    url = cluster().locked(ROWS, name)
    pg = PgEngine.connect(ROWS, url, 2)
    tenants = [2**63, 2**64 - 1, 2**63 - 1]
    for i, tenant in enumerate(tenants):
        pg.execute(tenant, Put([int_(i), NULL, NULL, NULL, NULL]))
    for i, tenant in enumerate(tenants):
        assert pg.execute(tenant, Read()) == [[int_(i), NULL, NULL, NULL, NULL]]
    with connect(cluster().admin_url(name)) as admin:
        stored = admin.execute('SELECT tenant_id, k FROM "odd ""näme"""').fetchall()
    assert sorted(stored) == [(MIN, 0), (-1, 1), (MAX, 2)]
