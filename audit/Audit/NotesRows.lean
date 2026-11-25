import Assay
import Audit.Except
import Audit.NotesGen
import Notes.Proofs

/-!
Breaks the row lists of the notes kernel and runs the theorems about writes on each broken
version.
-/

#assay Notes.Kernel.findMember Notes.Kernel.findNote Notes.Kernel.putMember Notes.Kernel.putNote
    Notes.Kernel.applyWrite
  using Notes.Kernel.findMember_applyWrite Notes.Kernel.findNote_applyWrite
    Notes.Kernel.users_putMember Notes.Kernel.ids_putNote Notes.Kernel.keyed_applyWrite
