"""The generated Python of the notes behind the memory engine against the kernel run natively by
Lean."""

import os
import subprocess
from pathlib import Path

from leanharbor import MemoryEngine, Refused
from leanharbor_notes import KERNEL, kernel, refusal_name

COMMANDS = Path(__file__).parents[2] / "testdata" / "notes-commands.txt"


def flag(word: str) -> bool:
    return {"0": False, "1": True}[word]


def parse(line: str) -> tuple[kernel.Principal, kernel.Command]:
    org, user, *rest = line.split(" ")
    actor = kernel.Principal(org=int(org), user=int(user))
    match rest:
        case ["add-member", u, admin]:
            return actor, kernel.Command_addMember(user=int(u), admin=flag(admin))
        case ["remove-member", u]:
            return actor, kernel.Command_removeMember(user=int(u))
        case ["put-note", i, shared, body]:
            return actor, kernel.Command_putNote(
                id=int(i), body=body, shared=flag(shared)
            )
        case ["delete-note", i]:
            return actor, kernel.Command_deleteNote(id=int(i))
        case ["read-note", i]:
            return actor, kernel.Command_readNote(id=int(i))
        case ["list-notes"]:
            return actor, kernel.Command_listNotes()
        case ["list-members"]:
            return actor, kernel.Command_listMembers()
    raise ValueError(line)


def bit(b: bool) -> str:
    return "1" if b else "0"


def note(n: kernel.Note) -> str:
    return f"{n.id}:{n.owner}:{bit(n.shared)}:{n.body}"


def show(reply: kernel.Reply) -> str:
    match reply:
        case kernel.Reply_done():
            return "done"
        case kernel.Reply_found(n=n):
            return f"found {note(n)}"
        case kernel.Reply_notes(ns=ns):
            return " ".join([f"notes {len(ns)}", *map(note, ns)])
        case kernel.Reply_members(ms=ms):
            return " ".join(
                [f"members {len(ms)}", *(f"{m.user}:{bit(m.admin)}" for m in ms)]
            )
    raise ValueError(reply)


def test_generated_python_agrees_with_lean() -> None:
    text = COMMANDS.read_text()
    oracle = subprocess.run(
        [os.environ["LEANHARBOR_NOTES_ORACLE"]],
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
            ours.append(f"ok {show(engine.execute(actor, cmd))}")
        except Refused as e:
            ours.append(f"error {refusal_name(e.error)}")
    assert len(ours) == 3000
    assert ours == oracle.splitlines()
