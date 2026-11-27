# Storing a kernel in PostgreSQL

A kernel declares its tables as a `List Tab` and each row type as an instance of
`Leangage.Row`, whose laws say that `fromRow` reads back what `toRow` writes and accepts no other
row. [`samples/lean/Calculator/Store.lean`](../samples/lean/Calculator/Store.lean) stores the
calculator's numbers in one table keyed by the user, each `UInt64` as the `Int64` with the same
bits:

```lean
def tables : List Tab := [⟨"memories", [⟨"user", .int, false⟩, ⟨"value", .int, false⟩], 1⟩]

def toRow (m : Memory) : List Val := [.int m.user.toInt64, .int m.value.toInt64]

def fromRow : List Val → Option Memory
  | [.int user, .int value] => some { user := user.toUInt64, value := value.toUInt64 }
  | _ => none

def writes : Option Memory → List Write
  | none => []
  | some m => [.put 0 1 (toRow m)]
```

`load` builds a snapshot from the rows of each table. A `Leangage.Storage` puts these together
with `enc`, the tenant's database a snapshot stands for, and 4 obligations: the schema is valid,
`init` stands for no rows, the rows an accepted write set stores turn the database of a snapshot
into that of the snapshot `apply` computes, and rows that list the database of a snapshot load to
a snapshot that stands for the same database.
[`samples/lean/Calculator/Store/Proofs.lean`](../samples/lean/Calculator/Store/Proofs.lean) proves
them for the calculator, and
[`samples/lean/Notes/Store/Proofs.lean`](../samples/lean/Notes/Store/Proofs.lean) for the notes,
whose members and notes are 2 tables, with `BOOLEAN` and `TEXT` columns. The tables and the row
functions are generated to the 3 servers. Those of the calculator run behind the 3 PostgreSQL
engines, and those of the notes behind the Rust one.

The Rust engine ([`langs/rust/leangage-pg`](../langs/rust/leangage-pg)) takes a kernel with an
implementation of `leangage::Storage`, which delegates `tables`, `load` and `writes` to the
generated functions. At start it creates the tables with the statements of the generated `create`
and `render`. Each command runs in one `SERIALIZABLE` transaction: the engine reads the tenant's row
of `leangage_version`, takes the snapshot it remembers for that version or else reads the tenant's
rows of each table with the generated `select` and builds the snapshot with `load`, calls
`transition`, and sends the statements the generated `compile` makes of the generated `plan` of
each write, with the values as parameters. A transaction that writes a row advances the tenant's
version by one, and after its commit the engine remembers the snapshot `apply` computed, at the new
version, for up to `Config::cache_tenants` tenants (1,024 by default). Its other statements are
constants of its own: the transaction control, the advisory locks, and the framework's tables
`leangage_idempotency`, which holds the reply of each command run under an idempotency key, per
tenant, scope and key, and `leangage_version`, which holds each tenant's version. `lockdown`,
which an administrator runs, writes statements of its own around role names it checks against
`[a-z_][a-z0-9_]*` and table names quoted by the generated `quote`. Its contract is the list at the
top of [`langs/rust/leangage-pg/src/lib.rs`](../langs/rust/leangage-pg/src/lib.rs).

The Python engine ([`langs/python/src/leangage/pg`](../langs/python/src/leangage/pg)) takes a
`leangage.Storage`, which the calculator fills with the generated `tables`, `load` and `writes`
of `store.py`. `store.py` is generated with the classes of the generated kernel and SQL compiler
(`--type-module`), so the snapshot `load` builds is the one `transition` takes, and the writes
`transition` returns are the ones `writes` takes. The engine keeps the same contract, at the top of
[`langs/python/src/leangage/pg/__init__.py`](../langs/python/src/leangage/pg/__init__.py), with the
same statements for the advisory locks, `leangage_idempotency` and `leangage_version` and the same
`lockdown`; it writes
its transaction control (`BEGIN ISOLATION LEVEL SERIALIZABLE`, `COMMIT`, `ROLLBACK`) itself, where
the Rust engine has tokio-postgres write it. It sends each value as a parameter of the type of its
kind (`BIGINT`, `BOOLEAN`, `TEXT`, `BYTEA`; `NULL` untyped) through psycopg's `RawCursor`, which
sends the text of `render` unchanged, and reads each column back by the OID of its type.

The Go engine ([`langs/go/leangage/pg`](../langs/go/leangage/pg), on pgx) takes a kernel with an
implementation of `leangage.Storage`, which the calculator implements with the generated
`Tables`, `Load` and `Writes` of the package `store`, generated with the types of the packages
`kernel` and `sql` (`--type-module`). The engine keeps the same contract, at the top of
[`langs/go/leangage/pg/pg.go`](../langs/go/leangage/pg/pg.go), with the statements of the Rust
engine for the transaction control, the advisory locks, `leangage_idempotency` and
`leangage_version`, and the same `Lockdown`; it keeps each remembered snapshot in a
`leanfran.Region` of its own and releases every snapshot it forgets. It
sends each value as a parameter of the type PostgreSQL inferred, which it checks against the
value's kind, and reads each column back by the OID of its type. The pool and the connections stay
inside the package: a kernel's code gets `Execute` and no type of pgx.

## The calculator's servers on PostgreSQL

With `LEANGAGE_DATABASE_URL`, the Rust, the Python and the Go servers keep the numbers in
PostgreSQL instead of their memory, and a server started again on the same database answers from
them. An administrator first runs one of them with `LEANGAGE_LOCKDOWN=<owner>:<engine role>`
and the administrator's connection string: it creates the tables, gives them to the owner (made
without the right to log in if it doesn't exist), lets the engine's role (which must exist and
may not be a superuser) read and write their rows but not alter, drop or truncate them, grants it
`USAGE` and `CREATE` on the schema (PostgreSQL checks `CREATE` before it finds that a table of
`CREATE TABLE IF NOT EXISTS` exists, and the engine runs those statements at start), and exits.
The database must exist too:

```console
$ export LEANGAGE_SECRET=dev-secret
$ TOKEN=$(cd samples/rust && LEANGAGE_ISSUE=1:7 cargo run --release -q --bin leangage-calculator)
$ psql -h /run/postgresql -U postgres -c 'CREATE DATABASE calc' -c 'CREATE ROLE leangage_engine LOGIN'
CREATE DATABASE
CREATE ROLE
$ (cd samples/rust && LEANGAGE_DATABASE_URL='host=/run/postgresql user=postgres dbname=calc' \
    LEANGAGE_LOCKDOWN=leangage_owner:leangage_engine cargo run --release -q --bin leangage-calculator)
$ cd samples/rust && LEANGAGE_DATABASE_URL='host=/run/postgresql user=leangage_engine dbname=calc' \
    LEANGAGE_LISTEN=127.0.0.1:8083 cargo run --release -q --bin leangage-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"apply","op":"add","arg":1}' 127.0.0.1:8083/rpc
{"value":1}
$ cd samples/python && LEANGAGE_DATABASE_URL='host=/run/postgresql user=leangage_engine dbname=calc' \
    LEANGAGE_LISTEN=127.0.0.1:8084 uv run python -m leangage_calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"apply","op":"add","arg":1}' 127.0.0.1:8084/rpc
{"value":2}
$ cd samples/go && LEANGAGE_DATABASE_URL='host=/run/postgresql user=leangage_engine dbname=calc' \
    LEANGAGE_LISTEN=127.0.0.1:8085 go run ./calculator/cmd/leangage-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"apply","op":"add","arg":1}' 127.0.0.1:8085/rpc
{"value":3}
```

The servers can run on one database at once. They read and write the same tables and the same
table of stored replies, and fingerprint a command alike, so a reply stored under an
`Idempotency-Key` by one is replayed by another.
