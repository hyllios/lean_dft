import DFT

/-!
# Axiom audit

Every declaration *defined in a module of this repository* (module name starting with `DFT`, `QM` or `ForMathlib`,
whatever its namespace) may depend only on `propext`, `Classical.choice` and `Quot.sound`.
A `sorry` shows up as `sorryAx` and fails the audit. Declarations in the file being checked are included too.

Run via `scripts/check_axioms.sh`; `scripts/test_axiom_check.sh` checks that the audit itself works.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ourRoots : List Name := [`DFT, `QM, `ForMathlib]
  let ours (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => ourRoots.any (·.isPrefixOf env.header.moduleNames[idx.toNat]!)
    | none => true   -- declared in the current file
  let names := env.constants.fold (fun acc n _ => acc.push n) (#[] : Array Name)
  let mut checked : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for name in names do
    if ours name && !name.isInternal then
      checked := checked + 1
      let axs ← liftCoreM <| collectAxioms name
      let extra := axs.filter (fun a => !allowed.contains a)
      if !extra.isEmpty then
        bad := bad.push (name, extra)
  if bad.isEmpty then
    logInfo m!"axiom check OK: {checked} declarations use only standard axioms"
  else
    for (n, axs) in bad do
      logError m!"{n} uses non-standard axioms {axs}"
