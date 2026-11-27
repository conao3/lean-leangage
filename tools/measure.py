"""Runs every speed measurement on this machine and writes `docs/speed.json`.

Writes the generated code first (`make generate`), so it needs make, lake and the leanfran
compilers on PATH (`tools/leanfran-compilers.sh` builds the compilers outside `nix develop`).
Needs cargo, go, uv and curl on PATH, and PostgreSQL's `initdb`, `pg_ctl` and `psql` on PATH or
in `/usr/lib/postgresql/<version>/bin`; installs `oha` with cargo when it is missing. Each
measurement runs alone. The PostgreSQL server runs, with its default settings, only during the
PostgreSQL measurements, in a temporary directory, on a Unix socket; as root, its programs run
as the user `postgres`. `tools/speed-charts.py` turns the result into charts and tables.
"""

import glob
import json
import os
import pwd
import re
import shutil
import socket
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GENERATORS = ["lake", "leanfran", "leanfran-python", "leanfran-go"]
ENGINE_RUNS = 3
HTTP_RUNS = 2
SECONDS = 8
BODIES = {"get": '{"cmd":"get"}', "apply": '{"cmd":"apply","op":"div","arg":1}'}
CONNECTIONS = [1, 64]
RUST_ROWS = {
    "generated kernel, Rust values": "Rust, generated kernel, snapshot as a Rust value",
    "generated kernel, Lean values": "Rust, generated kernel, snapshot as a Lean value",
    "memory engine": "Rust, memory engine",
    "handwritten Rust (not proved)": "Rust, a HashMap by hand (not proved)",
}
PG_ROW = "Rust, PostgreSQL engine"
PG_SIZES = ["1", "100", "1000", "10000"]
PG_SETTINGS = [
    "fsync",
    "synchronous_commit",
    "full_page_writes",
    "wal_level",
    "shared_buffers",
    "max_connections",
    "default_transaction_isolation",
]
LINE = re.compile(r"^\s*(.+?)\s+users=(\d+)\s+(\d+) ns/command$")


def run(
    cmd: list[str],
    cwd: Path,
    env: dict[str, str] | None = None,
    user: pwd.struct_passwd | None = None,
) -> str:
    owner = (
        {"user": user.pw_uid, "group": user.pw_gid, "extra_groups": []} if user else {}
    )
    done = subprocess.run(
        cmd,
        cwd=cwd,
        env={**os.environ, **(env or {})},
        check=True,
        capture_output=True,
        text=True,
        **owner,
    )
    return done.stdout


def postgres_bin() -> Path:
    """The directory of `initdb`, `pg_ctl` and `psql`: PATH's, or the newest Debian one."""
    names = ["initdb", "pg_ctl", "psql"]
    if all(shutil.which(name) for name in names):
        return Path(shutil.which("initdb")).parent
    found = [
        Path(d)
        for d in glob.glob("/usr/lib/postgresql/*/bin")
        if all((Path(d) / name).exists() for name in names)
    ]
    if not found:
        raise SystemExit(
            "PostgreSQL is required: put initdb, pg_ctl and psql on PATH "
            "or install it in /usr/lib/postgresql/<version>/bin (apt install postgresql)"
        )
    return max(
        found, key=lambda d: int(d.parent.name) if d.parent.name.isdigit() else 0
    )


def postgres_user() -> pwd.struct_passwd | None:
    """The user the PostgreSQL programs run as: this one, or `postgres` for root."""
    if os.geteuid() != 0:
        return None
    try:
        return pwd.getpwnam("postgres")
    except KeyError:
        raise SystemExit(
            "as root, PostgreSQL runs as the user postgres, which does not exist"
        )


class Postgres:
    """A server with the default settings in a temporary directory, on a Unix socket only."""

    def __init__(self, bin: Path) -> None:
        self.bin = bin
        self.user = postgres_user()
        self.dir = Path(tempfile.mkdtemp(prefix="leangage-measure-pg-", dir="/tmp"))
        if self.user:
            os.chown(self.dir, self.user.pw_uid, self.user.pw_gid)
        self.data = self.dir / "data"
        self.pg(
            [
                "initdb",
                "-D",
                str(self.data),
                "-U",
                "postgres",
                "--auth=trust",
                "-E",
                "UTF8",
            ]
        )
        options = f"-k {self.dir} -c listen_addresses=''"
        log = str(self.dir / "server.log")
        self.pg(
            ["pg_ctl", "-D", str(self.data), "-l", log, "-w", "-o", options, "start"]
        )

    def pg(self, cmd: list[str]) -> str:
        return run([str(self.bin / cmd[0])] + cmd[1:], self.dir, user=self.user)

    def sql(self, statement: str) -> str:
        return self.pg(
            ["psql", "-h", str(self.dir), "-U", "postgres", "-d", "postgres"]
            + ["-X", "-q", "-At", "-v", "ON_ERROR_STOP=1", "-c", statement]
        ).strip()

    def database(self, name: str) -> str:
        """Creates the empty database `name` and returns the superuser's connection string."""
        self.sql(f'DROP DATABASE IF EXISTS "{name}" WITH (FORCE)')
        self.sql(f'CREATE DATABASE "{name}"')
        return f"host={self.dir} user=postgres dbname={name}"

    def versions(self) -> dict[str, str]:
        listed = ", ".join(f"'{name}'" for name in PG_SETTINGS)
        rows = self.sql(
            f"SELECT name || '=' || current_setting(name) FROM pg_settings "
            f"WHERE name IN ({listed}) ORDER BY name"
        )
        return {
            "postgres": self.sql("SELECT version()"),
            "postgres settings": ", ".join(rows.splitlines()),
            "postgres data file system": run(
                ["stat", "-f", "-c", "%T", str(self.data)], self.dir
            ).strip(),
        }

    def stop(self) -> None:
        self.pg(["pg_ctl", "-D", str(self.data), "-m", "fast", "-w", "stop"])
        shutil.rmtree(self.dir)


def machine() -> str:
    cpu = next(
        line.split(":", 1)[1].strip()
        for line in Path("/proc/cpuinfo").read_text().splitlines()
        if line.startswith("model name")
    )
    kib = next(
        int(line.split()[1])
        for line in Path("/proc/meminfo").read_text().splitlines()
        if line.startswith("MemTotal")
    )
    return f"{os.cpu_count()} CPUs ({cpu}), {round(kib / 1048576)} GB of memory"


def versions() -> dict[str, str]:
    tools = {
        "rustc": ["rustc", "--version"],
        "go": ["go", "version"],
        "uv": ["uv", "--version"],
        "oha": ["oha", "--version"],
    }
    found = {name: run(cmd, ROOT / "samples/go").strip() for name, cmd in tools.items()}
    found["python"] = run(
        ["uv", "run", "python", "--version"], ROOT / "samples/python"
    ).strip()
    return found


def engine(
    out: dict[str, dict[str, list[int]]],
    cmd: list[str],
    cwd: Path,
    names: dict[str, str],
) -> None:
    for _ in range(ENGINE_RUNS):
        for line in run(cmd, cwd).splitlines():
            if (found := LINE.match(line)) and found[1] in names:
                out.setdefault(names[found[1]], {}).setdefault(found[2], []).append(
                    int(found[3])
                )


def postgres_engine(pg: Postgres) -> dict[str, dict[str, list[int]]]:
    """The bench's PostgreSQL row, each run on a database of its own."""
    runs: dict[str, list[int]] = {}
    for index in range(ENGINE_RUNS):
        url = pg.database(f"engine{index}")
        bench = [str(ROOT / "samples/rust/target/release/bench")]
        for line in run(bench, ROOT, {"LEANGAGE_DATABASE_URL": url}).splitlines():
            if (found := LINE.match(line)) and found[1] == "postgres engine":
                runs.setdefault(found[2], []).append(int(found[3]))
    if any(len(runs.get(size, [])) != ENGINE_RUNS for size in PG_SIZES):
        raise RuntimeError(f"the bench's postgres engine rows: {runs}")
    return {PG_ROW: runs}


def wait_for(port: int) -> None:
    for _ in range(200):
        with socket.socket() as probe:
            if probe.connect_ex(("127.0.0.1", port)) == 0:
                return
        time.sleep(0.1)
    raise RuntimeError(f"nothing listens on {port}")


def http(
    cmd: list[str], cwd: Path, env: dict[str, str], port: int, token: str
) -> dict[str, list[float]]:
    url = f"http://127.0.0.1:{port}/rpc"
    auth = f"Authorization: Bearer {token}"
    json_type = "Content-Type: application/json"
    server = subprocess.Popen(
        cmd,
        cwd=cwd,
        env={**os.environ, **env},
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    try:
        wait_for(port)
        first = run(
            [
                "curl",
                "-s",
                "-H",
                auth,
                "-H",
                json_type,
                "-d",
                '{"cmd":"set","value":6}',
                url,
            ],
            ROOT,
        )
        if json.loads(first) != {"value": 6}:
            raise RuntimeError(f"{cmd}: {first}")
        rates: dict[str, list[float]] = {}
        for _ in range(HTTP_RUNS):
            for connections in CONNECTIONS:
                for name, body in BODIES.items():
                    text = run(
                        [
                            "oha",
                            "-z",
                            f"{SECONDS}s",
                            "-c",
                            str(connections),
                            "--no-tui",
                            "-m",
                            "POST",
                        ]
                        + ["-H", auth, "-H", json_type, "-d", body, url],
                        ROOT,
                    )
                    codes = re.findall(r"\[(\d+)\] \d+ responses", text)
                    if codes != ["200"]:
                        raise RuntimeError(f"{cmd}: status codes {codes}")
                    case = f"{name}, {connections} connection{'s' if connections > 1 else ''}"
                    rates.setdefault(case, []).append(
                        float(re.search(r"Requests/sec:\s+([\d.]+)", text)[1])
                    )
        return rates
    finally:
        server.terminate()
        server.wait()


def main() -> None:
    pg_bin = postgres_bin()
    postgres_user()
    missing = [name for name in GENERATORS if shutil.which(name) is None]
    if missing:
        raise SystemExit(
            f"{', '.join(missing)} not on PATH: `make generate` needs lake and the leanfran "
            "compilers, which `tools/leanfran-compilers.sh` builds"
        )
    run(["make", "generate"], ROOT)
    if shutil.which("oha") is None:
        run(["cargo", "install", "oha"], ROOT)
    bins = Path(tempfile.mkdtemp())
    run(["cargo", "build", "--release"], ROOT / "samples/rust")
    run(["cargo", "build", "--release"], ROOT / "bench/rust")
    for module, package in [
        ("samples/go", "calculator/cmd/bench"),
        ("samples/go", "calculator/cmd/leangage-calculator"),
    ]:
        run(
            ["go", "build", "-o", str(bins / Path(package).name), f"./{package}"],
            ROOT / module,
        )
    for name in ["nethttp", "gin"]:
        run(["go", "mod", "tidy"], ROOT / "bench/go")
        run(["go", "build", "-o", str(bins / name), f"./cmd/{name}"], ROOT / "bench/go")
    run(["uv", "sync", "--quiet"], ROOT / "samples/python")
    run(["uv", "sync", "--quiet"], ROOT / "bench/python")

    commands: dict[str, dict[str, list[int]]] = {}
    engine(commands, [str(ROOT / "samples/rust/target/release/bench")], ROOT, RUST_ROWS)
    engine(
        commands, [str(bins / "bench")], ROOT, {"memory engine": "Go, memory engine"}
    )
    python_bench = ["uv", "run", "python", "-m", "leangage_calculator.bench"]
    engine(
        commands,
        python_bench,
        ROOT / "samples/python",
        {"memory engine execute": "Python, memory engine"},
    )

    secret = {"LEANGAGE_SECRET": "bench-secret"}
    rust_server = str(ROOT / "samples/rust/target/release/leangage-calculator")
    token = run([rust_server], ROOT, {**secret, "LEANGAGE_ISSUE": "1:7"}).strip()
    workers = str(os.cpu_count())
    baselines = ROOT / "bench/rust/target/release"
    servers = [
        ("leangage, Rust (axum)", [rust_server], ROOT, "LEANGAGE_LISTEN"),
        ("axum, no kernel", [str(baselines / "axum")], ROOT, "BENCH_LISTEN"),
        ("actix-web, no kernel", [str(baselines / "actix")], ROOT, "BENCH_LISTEN"),
        (
            "leangage, Go (net/http)",
            [str(bins / "leangage-calculator")],
            ROOT,
            "LEANGAGE_LISTEN",
        ),
        ("net/http, no kernel", [str(bins / "nethttp")], ROOT, "BENCH_LISTEN"),
        ("gin, no kernel", [str(bins / "gin")], ROOT, "BENCH_LISTEN"),
        (
            "leangage, Python (http.server)",
            ["uv", "run", "python", "-m", "leangage_calculator"],
            ROOT / "samples/python",
            "LEANGAGE_LISTEN",
        ),
        (
            f"FastAPI on uvicorn, {workers} processes, no kernel",
            [
                "uv",
                "run",
                "uvicorn",
                "fastapi_app:app",
                "--workers",
                workers,
                "--log-level",
                "warning",
                "--port",
                "{port}",
            ],
            ROOT / "bench/python",
            "",
        ),
        (
            f"Flask on gunicorn, {workers} processes, no kernel",
            [
                "uv",
                "run",
                "gunicorn",
                "-w",
                workers,
                "-b",
                "127.0.0.1:{port}",
                "flask_app:app",
            ],
            ROOT / "bench/python",
            "",
        ),
    ]
    replies = {}
    for index, (name, cmd, cwd, listen) in enumerate(servers):
        port = 18080 + index
        env = {**secret, listen: f"127.0.0.1:{port}"} if listen else {}
        replies[name] = http(
            [part.replace("{port}", str(port)) for part in cmd], cwd, env, port, token
        )

    pg = Postgres(pg_bin)
    try:
        pg_versions = pg.versions()
        pg_commands = postgres_engine(pg)
        pg_servers = [
            (
                "leangage, Rust (axum), PostgreSQL engine",
                [rust_server],
                "LEANGAGE_LISTEN",
                "LEANGAGE_DATABASE_URL",
            ),
            (
                "axum and tokio-postgres, no kernel",
                [str(baselines / "axum_postgres")],
                "BENCH_LISTEN",
                "BENCH_DATABASE_URL",
            ),
        ]
        pg_replies = {}
        for index, (name, cmd, listen, database) in enumerate(pg_servers):
            port = 18180 + index
            env = {
                **secret,
                listen: f"127.0.0.1:{port}",
                database: pg.database(f"http{index}"),
            }
            pg_replies[name] = http(cmd, ROOT, env, port, token)
    finally:
        pg.stop()

    result = {
        "machine": machine(),
        "versions": {**versions(), **pg_versions},
        "engine_ns_per_command": commands,
        "http_replies_per_second": replies,
        "postgres": {
            "engine_ns_per_command": pg_commands,
            "http_replies_per_second": pg_replies,
        },
    }
    (ROOT / "docs/speed.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
