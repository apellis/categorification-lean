import Categorification
import Lean.Util.CollectAxioms

/-! Audit every declaration defined by a Categorification module, including private declarations
and declarations added to upstream namespaces. Each check uses Lean's transitive axiom collector. -/

open Lean Elab Command

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← getEnv
  -- `moduleNames` maps the entire module table: compute it once, not once per declaration.
  let moduleNames := env.header.moduleNames
  let mut declarations : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some moduleIdx := env.getModuleIdxFor? name then
      if (`Categorification).isPrefixOf moduleNames[moduleIdx.toNat]! then
        declarations := declarations.push name
  if declarations.isEmpty then
    throwError "No Categorification declarations were imported"
  IO.println s!"Checking {declarations.size} Categorification declarations."
  let mut checked : Nat := 0
  for name in declarations do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
    checked := checked + 1
    if checked % 1000 == 0 then
      IO.println s!"Checked {checked}/{declarations.size} declarations."
  logInfo m!"Audited {checked} Categorification declarations; all transitive axioms are allowed."
