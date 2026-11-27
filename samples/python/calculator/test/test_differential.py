"""The generated Python behind the memory engine against the kernel run natively by Lean."""

import os
import subprocess
from pathlib import Path

from leangage import MemoryEngine, Refused
from leangage_calculator import KERNEL
from leangage_calculator.gen import kernel

COMMANDS = Path(__file__).parents[4] / "testdata" / "calculator-commands.txt"


def parse(line: str) -> tuple[kernel.Principal, kernel.Command]:
    org, user, *rest = line.split(" ")
    actor = kernel.Principal(org=int(org), user=int(user))
    match rest:
        case ["set", n]:
            return actor, kernel.Command_set(value=int(n))
        case ["apply", op, n]:
            return actor, kernel.Command_apply(op=kernel.Op(op), arg=int(n))
        case ["get"]:
            return actor, kernel.Command_get()
    raise ValueError(line)


def test_generated_python_agrees_with_lean() -> None:
    text = COMMANDS.read_text()
    oracle = subprocess.run(
        [os.environ["LEANGAGE_CALCULATOR_ORACLE"]],
        input=text,
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    engine = MemoryEngine(KERNEL)
    ours = []
    for line in text.splitlines():
        actor, cmd = parse(line)
        try:
            ours.append(f"ok {engine.execute(actor, cmd).v}")
        except Refused as e:
            ours.append(f"error {bytes(kernel.errorName(e.error)).decode()}")
    assert len(ours) == 5000
    assert ours == oracle.splitlines()
