import Categorification
-- The specification files are not imported by the library; audit their bindings as well.
import Categorification.Spec.Webster.Thm438
import Categorification.Spec.Webster.Prop55
import Categorification.Spec.Webster.Cor521
import Lean.Util.CollectAxioms

/-! Audit every declaration defined by a Categorification module, including private declarations
and declarations added to upstream namespaces. Each check uses Lean's transitive axiom collector.

The audit sees only loaded modules, so it first checks that every source file under
`Categorification/` is in the loaded module table. Run it from the repository root. -/

open Lean Elab Command

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← getEnv
  -- `moduleNames` maps the entire module table: compute it once, not once per declaration.
  let moduleNames := env.header.moduleNames
  -- A source file missing from the module table would escape the audit below.
  let loaded : NameSet := moduleNames.foldl (·.insert ·) {}
  let mut unloaded : Array Name := #[]
  for path in ← (System.FilePath.walkDir "Categorification" : IO _) do
    if path.extension == some "lean" then
      let module := (path.withExtension "").components.foldl Name.mkStr Name.anonymous
      unless loaded.contains module do
        unloaded := unloaded.push module
  unless unloaded.isEmpty do
    throwError "Source files whose modules are not imported, directly or transitively, by \
      Categorification.lean: {unloaded.qsort (·.toString < ·.toString)}"
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
