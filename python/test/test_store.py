"""The generated tables of the calculator and of the notes: they import, and they name the tables
and load the rows that Lean declares, as the kernels' own types."""

from leanharbor_calculator import store as calculator_store
from leanharbor_notes import kernel as notes_kernel
from leanharbor_notes import store as notes_store


def test_tables() -> None:
    assert [t.name for t in calculator_store.tables()] == ["memories"]
    assert [t.name for t in notes_store.tables()] == ["members", "notes"]


def test_notes_load() -> None:
    snapshot = notes_store.load([[], []])
    assert isinstance(snapshot, notes_kernel.Snapshot)
    assert (snapshot.members, snapshot.notes) == ([], [])
    assert notes_store.load([[[]], []]) is None
    assert notes_store.load([[]]) is None
