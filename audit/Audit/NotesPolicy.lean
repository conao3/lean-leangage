import Assay
import Audit.Except
import Audit.NotesGen
import Notes.Proofs

/-!
Breaks the policy of the notes kernel and runs the theorems about what each user may do on each
broken version.
-/

set_option assay.samples 300 in
#assay Notes.Kernel.isAdmin Notes.Kernel.permits Notes.Kernel.visible Notes.Kernel.stored
    Notes.Kernel.view Notes.Kernel.disclosed Notes.Kernel.readOnly
  using Notes.Kernel.transition_authorized_run Notes.Kernel.others_unchanged_run
    Notes.Kernel.members_unchanged_run Notes.Kernel.admin_not_denied Notes.Kernel.owner_may_put
    Notes.Kernel.owner_may_delete Notes.Kernel.first_member Notes.Kernel.read_after_put_run
    Notes.Kernel.read_note_spec Notes.Kernel.list_notes_spec Notes.Kernel.list_members_spec
    Notes.Kernel.rows_stored_run
