"""Runs every speed measurement on this machine and writes `docs/speed.json`.

Needs cargo, go, uv and curl on PATH; installs `oha` with cargo when it is missing. Each
measurement runs alone. `tools/speed-charts.py` turns the result into charts and tables.
"""

import json
import os
import re
import shutil
import socket
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ENGINE_RUNS = 3
HTTP_RUNS = 2
SECONDS = 8
BODIES = {"get": '{"cmd":"get"}', "apply": '{"cmd":"apply","op":"div","arg":1}'}
CONNECTIONS = [1, 64]
RUST_ROWS = {
    "generated kernel, Rust values": "Rust, generated kernel, snapshot as a Rust value",
    "generated kernel, Lean values": "Rust, generated kernel, snapshot as a Lean value",
    "memory engine": "Rust, memory engine",
    "handwritten Rust (not proved)": "Rust, the same logic by hand (not proved)",
}
LINE = re.compile(r"^\s*(.+?)\s+users=(\d+)\s+(\d+) ns/command$")


def run(cmd: list[str], cwd: Path, env: dict[str, str] | None = None) -> str:
    done = subprocess.run(
        cmd,
        cwd=cwd,
        env={**os.environ, **(env or {})},
        check=True,
        capture_output=True,
        text=True,
    )
    return done.stdout


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
    found = {name: run(cmd, ROOT / "go").strip() for name, cmd in tools.items()}
    found["python"] = run(["uv", "run", "python", "--version"], ROOT / "python").strip()
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
    if shutil.which("oha") is None:
        run(["cargo", "install", "oha"], ROOT)
    bins = Path(tempfile.mkdtemp())
    run(["cargo", "build", "--release"], ROOT / "rust")
    run(["cargo", "build", "--release"], ROOT / "bench/rust")
    for module, package in [
        ("go", "calculator/cmd/bench"),
        ("go", "calculator/cmd/leanharbor-calculator"),
    ]:
        run(
            ["go", "build", "-o", str(bins / Path(package).name), f"./{package}"],
            ROOT / module,
        )
    for name in ["nethttp", "gin"]:
        run(["go", "mod", "tidy"], ROOT / "bench/go")
        run(["go", "build", "-o", str(bins / name), f"./cmd/{name}"], ROOT / "bench/go")
    run(["uv", "sync", "--quiet"], ROOT / "python")
    run(["uv", "sync", "--quiet"], ROOT / "bench/python")

    commands: dict[str, dict[str, list[int]]] = {}
    engine(commands, [str(ROOT / "rust/target/release/bench")], ROOT, RUST_ROWS)
    engine(
        commands, [str(bins / "bench")], ROOT, {"memory engine": "Go, memory engine"}
    )
    python_bench = ["uv", "run", "python", "-m", "leanharbor_calculator.bench"]
    engine(
        commands,
        python_bench,
        ROOT / "python",
        {"memory engine execute": "Python, memory engine"},
    )

    secret = {"LEANHARBOR_SECRET": "bench-secret"}
    rust_server = str(ROOT / "rust/target/release/leanharbor-calculator")
    token = run([rust_server], ROOT, {**secret, "LEANHARBOR_ISSUE": "1:7"}).strip()
    workers = str(os.cpu_count())
    baselines = ROOT / "bench/rust/target/release"
    servers = [
        ("leanharbor, Rust (axum)", [rust_server], ROOT, "LEANHARBOR_LISTEN"),
        ("axum, no kernel", [str(baselines / "axum")], ROOT, "BENCH_LISTEN"),
        ("actix-web, no kernel", [str(baselines / "actix")], ROOT, "BENCH_LISTEN"),
        (
            "leanharbor, Go (net/http)",
            [str(bins / "leanharbor-calculator")],
            ROOT,
            "LEANHARBOR_LISTEN",
        ),
        ("net/http, no kernel", [str(bins / "nethttp")], ROOT, "BENCH_LISTEN"),
        ("gin, no kernel", [str(bins / "gin")], ROOT, "BENCH_LISTEN"),
        (
            "leanharbor, Python (http.server)",
            ["uv", "run", "leanharbor-calculator"],
            ROOT / "python",
            "LEANHARBOR_LISTEN",
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

    result = {
        "machine": machine(),
        "versions": versions(),
        "engine_ns_per_command": commands,
        "http_replies_per_second": replies,
    }
    (ROOT / "docs/speed.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
