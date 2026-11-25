import Assay
import Audit.Except
import Audit.NotesGen
import Notes.Proofs

/-!
Breaks the row lists of the notes kernel and the sorts of its listings, and runs the theorems about
writes and listings on each broken version.
-/

#assay Notes.Kernel.findMember Notes.Kernel.findNote Notes.Kernel.putMember Notes.Kernel.putNote
    Notes.Kernel.applyWrite Notes.Kernel.insertMember Notes.Kernel.sortMembers
    Notes.Kernel.insertNote Notes.Kernel.sortNotes
  using Notes.Kernel.findMember_applyWrite Notes.Kernel.findNote_applyWrite
    Notes.Kernel.users_putMember Notes.Kernel.ids_putNote Notes.Kernel.keyed_applyWrite
    Notes.Kernel.insertMember_eq Notes.Kernel.insertNote_eq Notes.Kernel.sortMembers_eq
    Notes.Kernel.sortNotes_eq Notes.Kernel.sortMembers_spec Notes.Kernel.sortNotes_spec
    Notes.Kernel.list_notes_spec Notes.Kernel.list_members_spec
