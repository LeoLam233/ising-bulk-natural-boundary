import IsingBulk
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let projectModule := fun name : Name =>
    match env.getModuleIdxFor? name with
    | some idx => (`IsingBulk).isPrefixOf env.header.moduleNames[idx.toNat]!
    | none => false
  let entries := env.constants.toList.filter fun (name, _) => projectModule name
  for (name, info) in entries do
    if info.isTheorem && info.isUnsafe then
      throwError "Unexpected unsafe theorem: {name}"
    if info.isAxiom then
      throwError "Unexpected project axiom: {name}"
  let safeEntries := entries.filter fun (_, info) => !info.isUnsafe
  let names := safeEntries.map Prod.fst
  let mut axioms : NameSet := {}
  for name in names do
    let axs ← Lean.collectAxioms name
    logInfo m!"DECLARATION: {name}; AXIOMS: {axs}"
    for ax in axs do
      axioms := axioms.insert ax
  for ax in axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unapproved reachable logical axiom: {ax}"
  logInfo m!"AXIOM UNION: {axioms.toArray.qsort Name.lt}"
  logInfo m!"AUDIT PASSED: {names.length} kernel-safe project declarations"
