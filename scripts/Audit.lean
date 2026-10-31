import GlobalRegularization
import Lean.Util.CollectAxioms

/-! Reject unproved axioms (including `sorryAx`) in the transitive
dependencies of every declaration in this project's namespace. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, _) =>
    if (`GlobalRegularization).isPrefixOf name then some name else none
  let action : CollectAxioms.M Unit := do
    for name in names do
      CollectAxioms.collect name
  let (_, state) := (action.run env).run {}
  let permitted := #[`propext, `Quot.sound, `Classical.choice]
  for axiomName in state.axioms do
    unless permitted.contains axiomName do
      throwError "Unapproved axiom in project dependencies: {axiomName}"
  logInfo m!"Axiom audit passed for {names.length} declarations. Dependencies: {state.axioms}"
