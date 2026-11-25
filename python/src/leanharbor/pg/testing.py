"""A PostgreSQL server for tests, in a temporary directory, one per test process.

`cluster` runs `initdb` and starts the server on a Unix socket in that directory, with the roles
`OWNER` (no login) and `ENGINE_ROLE` (login, not a superuser). A shell started with the server
waits on a pipe from the test process; when the process exits, however it exits, the pipe closes
and the shell stops the server and removes the directory. `initdb`, `pg_ctl` and `psql` come from
`PATH` (the flake's devShell); a test that cannot start the server fails.
"""

import os
import subprocess
import threading
import time
from pathlib import Path
from typing import Any

import psycopg

from leanharbor.engine import Storage
from leanharbor.pg import lockdown

# The role that owns the tables.
OWNER = "leanharbor_owner"
# The role the engine logs in as.
ENGINE_ROLE = "leanharbor_engine"

SUPERVISOR = r"""
set -eu
dir=$1
trap 'pg_ctl -D "$dir/data" -m immediate stop >/dev/null 2>&1 || true; rm -rf "$dir"' EXIT
initdb -D "$dir/data" -U postgres --auth=trust --no-sync -E UTF8 >"$dir/initdb.log" 2>&1
pg_ctl -D "$dir/data" -l "$dir/server.log" -w -o "-k $dir -c listen_addresses='' -c fsync=off -c synchronous_commit=off -c full_page_writes=off -c max_connections=300" start >/dev/null
psql -h "$dir" -U postgres -d postgres -X -q -v ON_ERROR_STOP=1 -c "CREATE ROLE leanharbor_owner NOLOGIN" -c "CREATE ROLE leanharbor_engine LOGIN"
echo ready
read _ || true
"""


class Cluster:
    """`dir` is the data directory's parent, where the server's socket is."""

    def __init__(self, dir: Path, supervisor: subprocess.Popen[bytes]) -> None:
        self.dir = dir
        self._supervisor = supervisor

    def url(self, user: str, database: str) -> str:
        """A connection string for `user` to `database`."""
        return f"host={self.dir} user={user} dbname={database}"

    def admin_url(self, database: str) -> str:
        """The superuser's connection string to `database`."""
        return self.url("postgres", database)

    def socket(self) -> Path:
        """The Unix socket of the server."""
        return self.dir / ".s.PGSQL.5432"

    def database(self, name: str) -> str:
        """Creates the empty database `name`, dropping one of that name, and returns the engine
        role's connection string to it."""
        with connect(self.admin_url("postgres")) as admin:
            admin.execute(f'DROP DATABASE IF EXISTS "{name}" WITH (FORCE)')
            admin.execute(f'CREATE DATABASE "{name}"')
        return self.url(ENGINE_ROLE, name)

    def locked(self, storage: Storage, name: str) -> str:
        """`database`, with the tables of `storage` made by `lockdown`."""
        url = self.database(name)
        lockdown(storage, self.admin_url(name), OWNER, ENGINE_ROLE)
        return url


_cluster: Cluster | None = None
_lock = threading.Lock()


def cluster() -> Cluster:
    """The server of this test process, started on the first call."""
    global _cluster
    with _lock:
        if _cluster is None:
            _cluster = _start()
        return _cluster


def _start() -> Cluster:
    dir = Path(f"/tmp/leanharbor-pg-{os.getpid()}-{time.time_ns() % 1_000_000_000}")
    dir.mkdir()
    supervisor = subprocess.Popen(
        ["sh", "-c", SUPERVISOR, "sh", str(dir)],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    assert supervisor.stdout is not None
    line = supervisor.stdout.readline()
    if line.strip() != b"ready":
        _, err = supervisor.communicate()

        def log(name: str) -> str:
            path = dir / name
            return path.read_text() if path.exists() else ""

        raise RuntimeError(
            "PostgreSQL did not start (initdb, pg_ctl and psql must be on PATH):\n"
            f"{err.decode()}\n{log('initdb.log')}\n{log('server.log')}"
        )
    return Cluster(dir, supervisor)


def connect(url: str) -> psycopg.Connection[Any]:
    """A connection that runs each statement on its own, with `$1`, `$2`, ... for the
    parameters."""
    return psycopg.connect(url, autocommit=True, cursor_factory=psycopg.RawCursor)
