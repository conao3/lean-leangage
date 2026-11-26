import Lean
import Leangage.Obligation

/-!
# The obligation check

Based on the obligation check of h5i's gate program in `crates/h5i-app-cli/src/check.rs`
(https://github.com/h5i-dev/h5i, commit 515c7b9, Apache-2.0). Changed: it is a command run in the
build instead of a program `h5i app check` writes, and it finds the theorems by searching the
environment instead of reading their names from a manifest.

`#obligations k` fails the build unless, for each statement of `Leangage.Obligation` about the
kernel `k`, a theorem states it and depends only on `propext`, `Classical.choice` and
`Quot.sound`. A theorem states an obligation when its type, once the arguments the kernel chooses
are filled in by unification, is definitionally equal to the statement in Lean's kernel
(`Kernel.isDefEq`). The statements are:

- `ReadOnlySound k _`, for every kernel. The write list is the kernel's choice, and the check
  prints the statement with it filled in;
- `Invariant k I`, for each `I` given after `invariant`.

The theorems searched are those of the file the command is in and of every imported module
outside `Init`, `Std`, `Lean` and `Lake`, without universe parameters.
-/

open Lean Elab Command Term Meta

namespace Audit.Obligations

/-- The axioms a theorem that states an obligation may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The theorems the check searches, with their types. -/
def candidates (env : Environment) : Array (Name × Expr) :=
  env.constants.fold (init := #[]) fun acc n ci =>
    match ci with
    | .thmInfo t =>
      let core := match env.getModuleIdxFor? n with
        | some idx =>
          [`Init, `Std, `Lean, `Lake].contains (env.header.moduleNames[idx.toNat]!.getRoot)
        | none => false
      if core || !t.levelParams.isEmpty then acc else acc.push (n, t.type)
    | _ => acc

/-- What a theorem whose type unifies with an obligation's statement gives. -/
inductive Found where
  /-- The statement with the kernel's choices filled in, equal to the theorem's type in Lean's
  kernel. -/
  | states (stmt : Expr)
  /-- Unification leaves part of the statement open. -/
  | undetermined

/-- Whether the theorem's type `type` is the statement `stmt`, a closed term whose leading
`fun` binders are the arguments the kernel chooses. -/
def compare (stmt type : Expr) : MetaM (Option Found) :=
  withoutModifyingState do
    try
      let (_, _, expected) ← lambdaMetaTelescope stmt
      unless ← isDefEq expected type do return none
      let e ← instantiateMVars expected
      if e.hasMVar || e.hasLevelMVar then return some .undetermined
      match Kernel.isDefEq (← getEnv) {} e type with
      | .ok true => return some (.states e)
      | _ => return none
    catch _ => return none

/-- Checks one obligation, given as syntax, against every candidate. Returns the line to print
when a theorem states it, or the error. `holes` is the number of arguments the kernel chooses. -/
def check (cands : Array (Name × Expr)) (label : MessageData) (stx : Term) (holes : Nat) :
    TermElabM (Except MessageData MessageData) := do
  let e ← elabTerm stx (some (.sort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let r ← abstractMVars (← instantiateMVars e)
  if !r.paramNames.isEmpty then
    return .error m!"{label}: the statement `{stx}` has a universe the kernel would choose"
  if r.numMVars != holes then
    return .error m!"{label}: the statement `{stx}` has {r.numMVars} holes, and it may have {holes}"
  let mut good : Array MessageData := #[]
  let mut bad : Array MessageData := #[]
  for (n, type) in cands do
    match ← compare r.expr type with
    | none => pure ()
    | some .undetermined =>
      bad := bad.push m!"{n} leaves part of the statement undetermined"
    | some (.states stmt) =>
      let axs := (← collectAxioms n).filter (!allowedAxioms.contains ·)
      if axs.isEmpty then
        good := good.push m!"{n} states {stmt}"
      else
        bad := bad.push m!"{n} states it but depends on the axioms {axs.toList}"
  if good.isEmpty then
    let found := if bad.isEmpty then m!"" else m!"\n" ++ MessageData.joinSep bad.toList "\n"
    return .error m!"{label}: no theorem states `{stx}` with only the standard axioms{found}"
  return .ok (m!"{label}: " ++ MessageData.joinSep good.toList ", ")

/-- `#obligations k` checks the statements of `Leangage.Obligation` for the kernel `k`, and
`#obligations k invariant I₁ I₂` checks `Invariant k I₁` and `Invariant k I₂` as well. -/
syntax (name := obligations) "#obligations " ident (" invariant" (ppSpace term:max)+)? : command

@[command_elab obligations]
def elabObligations : CommandElab
  | `(#obligations $k:ident $[invariant $is*]?) => do
    let cands := candidates (← getEnv)
    let stmts : Array (MessageData × Term × Nat) :=
      #[(m!"ReadOnlySound", ← `($(mkIdent ``Leangage.Obligation.ReadOnlySound) $k _), 2)] ++
        (← (is.getD #[]).mapM fun i => do
          return (m!"Invariant {i}", ← `($(mkIdent ``Leangage.Obligation.Invariant) $k $i), 0))
    let mut lines : Array MessageData := #[]
    let mut failed := false
    for (label, stx, holes) in stmts do
      match ← liftTermElabM (check cands label stx holes) with
      | .ok line => lines := lines.push line
      | .error msg => logErrorAt k msg; failed := true
    unless failed do
      logInfo (MessageData.joinSep lines.toList "\n")
  | _ => throwUnsupportedSyntax

end Audit.Obligations
