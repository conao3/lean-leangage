"""The calculator on the PostgreSQL engine: the generated Python table functions behind it give
every command the reply the memory engine and Lean give it, alone and from many threads, and the
commands of one tenant leave the rows of the others as they were; a server started again on the
same database answers from the state the first one stored; and the Rust and the Python server
share a database, each answering from the rows and the stored replies of the other."""

import http.client
import json
import os
import socket
import subprocess
import sys
import time
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from typing import Any

from leanharbor import Claims, MemoryEngine, Refused, issue
from leanharbor.pg import Config, PgEngine
from leanharbor.pg.testing import ENGINE_ROLE, OWNER, cluster, connect
from leanharbor_calculator import KERNEL, STORAGE, kernel
from test_differential import COMMANDS, parse

SECRET = "secret"


def line(engine: Any, actor: kernel.Principal, cmd: kernel.Command) -> str:
    try:
        return f"ok {engine.execute(actor, cmd).v}"
    except Refused as e:
        return f"error {bytes(kernel.errorName(e.error)).decode()}"


def oracle() -> list[str]:
    return subprocess.run(
        [os.environ["LEANHARBOR_CALCULATOR_ORACLE"]],
        input=COMMANDS.read_text(),
        capture_output=True,
        text=True,
        check=True,
    ).stdout.splitlines()


def commands() -> list[tuple[kernel.Principal, kernel.Command]]:
    return [parse(text) for text in COMMANDS.read_text().splitlines()]


def run(engine: Any) -> list[str]:
    return [line(engine, actor, cmd) for actor, cmd in commands()]


Rows = dict[tuple[int, int], int]


def rows(admin: Any) -> Rows:
    stored = admin.execute('SELECT tenant_id, "user", value FROM memories').fetchall()
    return {(t, u): v for t, u, v in stored}


def others(r: Rows, mine: tuple[int, int]) -> Rows:
    return {k: v for k, v in r.items() if k != mine}


# The rows stored and read back in PostgreSQL give every command the reply the memory engine and
# Lean give it: PostgreSQL runs the generated statements as the model of `Leanharbor.Sql` says.
# The command list mixes three tenants; after each command, every row of the other tenants, and
# of the other users of its tenant, is as it was.
def test_postgres_engine_agrees_with_memory_engine_and_lean() -> None:
    name = "calculator_differential"
    url = cluster().locked(STORAGE, name)
    engine = PgEngine.connect(STORAGE, url, 2)
    ours = []
    tenants = set()
    with connect(cluster().admin_url(name)) as admin:
        before = rows(admin)
        for actor, cmd in commands():
            tenants.add(actor.org)
            mine = (actor.org, actor.user)
            ours.append(line(engine, actor, cmd))
            after = rows(admin)
            assert others(after, mine) == others(before, mine), (actor, cmd)
            before = after
    assert len(tenants) == 3
    assert len({t for t, _ in before}) == 3
    assert len(ours) == 5000
    assert ours == run(MemoryEngine(KERNEL))
    assert ours == oracle()
    assert engine.stats.retries == 0


def client(
    engine: PgEngine,
    listed: list[tuple[kernel.Principal, kernel.Command]],
    indices: list[int],
    ours: list[str],
) -> None:
    """Runs the commands at `indices` in order, and writes each line in `ours`."""
    for i in indices:
        actor, cmd = listed[i]
        ours[i] = line(engine, actor, cmd)


# Each principal's commands, from a thread of its own, with and without the advisory lock: a
# command reads and writes only its user's row, so each reply is the one Lean gives it in the
# order of the list.
def test_concurrent_principals_agree_with_lean() -> None:
    expected = oracle()
    by_principal: dict[tuple[int, int], list[int]] = defaultdict(list)
    listed = commands()
    for i, (actor, _) in enumerate(listed):
        by_principal[(actor.org, actor.user)].append(i)
    assert len(by_principal) == 15
    for lock in [True, False]:
        url = cluster().locked(STORAGE, f"calculator_concurrent_{lock}".lower())
        engine = PgEngine.connect(STORAGE, url, 8, Config(1000, lock, None))
        ours = [""] * len(listed)
        with ThreadPoolExecutor(len(by_principal)) as pool:
            futures = [
                pool.submit(client, engine, listed, indices, ours)
                for indices in by_principal.values()
            ]
            for f in futures:
                f.result()
        assert ours == expected, f"lock {lock}"


def free_port() -> int:
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


class Server:
    """A calculator server in a process of its own, on `LEANHARBOR_DATABASE_URL`."""

    def __init__(self, argv: list[str], url: str) -> None:
        self.port = free_port()
        env = {
            **os.environ,
            "LEANHARBOR_SECRET": SECRET,
            "LEANHARBOR_LISTEN": f"127.0.0.1:{self.port}",
            "LEANHARBOR_DATABASE_URL": url,
        }
        self.process = subprocess.Popen(argv, env=env)
        deadline = time.monotonic() + 20
        while True:
            try:
                socket.create_connection(("127.0.0.1", self.port)).close()
                break
            except OSError:
                assert self.process.poll() is None, "the server runs"
                assert time.monotonic() < deadline, "the server listens"
                time.sleep(0.02)
        self.connection = http.client.HTTPConnection("127.0.0.1", self.port)

    def post(
        self, token: str, body: dict[str, Any], key: str | None = None
    ) -> tuple[int, str]:
        """`POST /rpc`: the status and the body."""
        headers = {
            "Authorization": f"Bearer {token}",
            "Content-Type": "application/json",
        }
        if key is not None:
            headers["Idempotency-Key"] = key
        self.connection.request("POST", "/rpc", json.dumps(body), headers)
        response = self.connection.getresponse()
        return response.status, response.read().decode()

    def stop(self) -> None:
        self.connection.close()
        self.process.kill()
        self.process.wait()


PYTHON_SERVER = [sys.executable, "-m", "leanharbor_calculator"]


def rust_server() -> list[str]:
    return [os.environ["LEANHARBOR_RUST_CALCULATOR"]]


def token(tenant: int, user: int) -> str:
    return issue(SECRET.encode(), Claims(tenant, user, int(time.time()) + 86_400))


def run_lockdown(argv: list[str], name: str) -> None:
    """`LEANHARBOR_LOCKDOWN` with the administrator's connection string makes the tables, and
    the server then runs as the engine's role."""
    env = {
        **os.environ,
        "LEANHARBOR_SECRET": SECRET,
        "LEANHARBOR_DATABASE_URL": cluster().admin_url(name),
        "LEANHARBOR_LOCKDOWN": f"{OWNER}:{ENGINE_ROLE}",
    }
    subprocess.run(argv, env=env, check=True)


def test_state_survives_a_restart_of_the_server() -> None:
    name = "calculator_restart"
    url = cluster().database(name)
    run_lockdown(PYTHON_SERVER, name)
    a, b = token(1, 7), token(2, 7)
    first = Server(PYTHON_SERVER, url)
    try:
        assert first.post(a, {"cmd": "set", "value": 6}) == (200, '{"value":6}')
        assert first.post(a, {"cmd": "apply", "op": "mul", "arg": 7}) == (
            200,
            '{"value":42}',
        )
        assert first.post(a, {"cmd": "apply", "op": "div", "arg": 0}) == (
            422,
            '{"error":"division_by_zero"}',
        )
        assert first.post(b, {"cmd": "set", "value": 5}) == (200, '{"value":5}')
    finally:
        first.stop()
    second = Server(PYTHON_SERVER, url)
    try:
        assert second.post(a, {"cmd": "get"}) == (200, '{"value":42}')
        assert second.post(b, {"cmd": "get"}) == (200, '{"value":5}')
        assert second.post(token(1, 8), {"cmd": "get"}) == (200, '{"value":0}')
    finally:
        second.stop()
    with connect(cluster().admin_url(name)) as admin:
        row = admin.execute(
            "SELECT tableowner FROM pg_tables WHERE tablename = 'memories'"
        ).fetchone()
    assert row == (OWNER,)


def body(text: str) -> dict[str, Any]:
    match text.split(" ")[2:]:
        case ["set", n]:
            return {"cmd": "set", "value": int(n)}
        case ["apply", op, n]:
            return {"cmd": "apply", "op": op, "arg": int(n)}
        case ["get"]:
            return {"cmd": "get"}
    raise ValueError(text)


def expected(answer: str) -> tuple[int, str]:
    kind, value = answer.split(" ")
    if kind == "ok":
        return 200, f'{{"value":{value}}}'
    return 422, f'{{"error":"{value}"}}'


# The Rust server makes the tables, and the two servers run on them at once: the commands of
# the list go to the Rust and the Python server in turn, so each reads what the other stored, and
# every reply is the one Lean gives. A key used on one server replays its reply on
# the other, and the other refuses it with another command.
def test_rust_and_python_servers_share_a_database() -> None:
    name = "calculator_shared"
    url = cluster().database(name)
    run_lockdown(rust_server(), name)
    rust = Server(rust_server(), url)
    python = Server(PYTHON_SERVER, url)
    try:
        servers = [rust, python]
        tokens: dict[tuple[str, str], str] = {}
        texts = COMMANDS.read_text().splitlines()
        answers = oracle()
        assert len(texts) == 5000
        for i, (text, answer) in enumerate(zip(texts, answers, strict=True)):
            org, user = text.split(" ")[:2]
            t = tokens.setdefault((org, user), token(int(org), int(user)))
            assert servers[i % 2].post(t, body(text)) == expected(answer), (i, text)

        a = token(9, 1)
        add = {"cmd": "apply", "op": "add", "arg": 5}
        for first, second, key in [(rust, python, "r"), (python, rust, "p")]:
            assert first.post(a, add, key)[0] == 200
            reply = first.post(a, {"cmd": "get"})
            assert second.post(a, add, key) == reply, "replayed, not run again"
            assert second.post(a, {"cmd": "get"}) == reply
            assert second.post(a, {"cmd": "set", "value": 1}, key) == (
                422,
                '{"error":"idempotency key reused"}',
            )
        assert python.post(a, {"cmd": "get"}) == (200, '{"value":10}')
    finally:
        rust.stop()
        python.stop()
