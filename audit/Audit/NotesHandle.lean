import Assay
import Audit.Except
import Audit.NotesGen
import Notes.Proofs

/-!
Breaks the handlers of the notes kernel and runs the theorems about what each command does on
each broken version.
-/

set_option assay.samples 300 in
#assay Notes.Kernel.handle Notes.Kernel.apply Notes.Kernel.textOk
  using Notes.Kernel.transition_authorized_run Notes.Kernel.read_after_put_run
    Notes.Kernel.read_after_delete_run Notes.Kernel.member_after_add_run
    Notes.Kernel.member_after_remove_run Notes.Kernel.bad_text Notes.Kernel.not_found
    Notes.Kernel.read_note_spec Notes.Kernel.list_notes_spec Notes.Kernel.list_members_spec
    Notes.Kernel.rows_stored_run Notes.Kernel.admin_not_denied
