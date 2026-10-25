import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Strict audit support. This module contains tooling, not a mathematical premise.
The final logical closure is scanned through actual types AND values, including
opaque values. Partial generated helpers are inventoried separately and cannot
be silently skipped if reachable from a theorem root. -/
namespace JointAudit
open Lean Elab Command

def allowedAxiom (name : Name) : Bool :=
  name == `propext || name == `Classical.choice || name == `Quot.sound

def scanActualClosure (roots : Array Name) (required : Array Name := #[]) : CommandElabM Unit := do
  let env ← getEnv
  for name in roots do
    let some info := env.checked.get.find? name | throwError "JOINT missing endpoint: {name}"
    unless info.isTheorem do throwError "JOINT endpoint is not a theorem: {name}"
    logInfo m!"JOINT_ENDPOINT_TYPE: {name}; {info.type}"
    let axioms ← Lean.collectAxioms name
    logInfo m!"JOINT_ENDPOINT_AXIOMS: {name}; {axioms}"
    for ax in axioms do
      unless allowedAxiom ax do throwError "JOINT unapproved endpoint axiom: {name}; {ax}"
  let mut todo := roots.toList
  let mut seen : NameSet := {}
  let mut logicalModules : NameSet := {}
  let mut opaqueCount : Nat := 0
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name | throwError "JOINT missing logical dependency: {name}"
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if (`IsingBulk).isPrefixOf modName then logicalModules := logicalModules.insert modName
    if info.isUnsafe then throwError "JOINT unsafe logical dependency: {name}"
    if info.isPartial then throwError "JOINT partial logical dependency: {name}"
    if info.isAxiom && !allowedAxiom name then throwError "JOINT unapproved logical axiom: {name}"
    let types := info.type.getUsedConstants.toList
    let values := match info.value? true with
      | some value => value.getUsedConstants.toList
      | none => []
    todo := types ++ values ++ todo
    if let .inductInfo value := info then todo := value.ctors ++ todo
    if let .opaqueInfo _ := info then opaqueCount := opaqueCount + 1
    if (`IsingBulk).isPrefixOf name then
      logInfo m!"JOINT_LOGICAL_EDGE: {name}; TYPE: {types}; VALUE: {values}"
  for name in required do
    unless seen.contains name do throwError "JOINT required mathematical mechanism absent from actual closure: {name}"
  let projectModule := fun name : Name => match env.getModuleIdxFor? name with
    | some idx => (`IsingBulk).isPrefixOf env.header.moduleNames[idx.toNat]!
    | none => (`IsingBulk).isPrefixOf name
  let mut projectCount : Nat := 0
  let mut partialNames : Array Name := #[]
  let mut unsafeNames : Array Name := #[]
  let mut opaqueNames : Array Name := #[]
  for (name,info) in env.constants.toList do
    unless projectModule name do continue
    projectCount := projectCount + 1
    if info.isPartial then partialNames := partialNames.push name
    if info.isUnsafe then unsafeNames := unsafeNames.push name
    if let .opaqueInfo _ := info then opaqueNames := opaqueNames.push name
    if info.isAxiom && !allowedAxiom name then throwError "JOINT project axiom: {name}"
  logInfo m!"JOINT_PROJECT_PARTIAL_INVENTORY: {partialNames.qsort Name.lt}"
  logInfo m!"JOINT_PROJECT_UNSAFE_INVENTORY: {unsafeNames.qsort Name.lt}"
  logInfo m!"JOINT_PROJECT_OPAQUE_INVENTORY: {opaqueNames.qsort Name.lt}"
  logInfo m!"JOINT_ACTUAL_LOGICAL_MODULES: {logicalModules.toArray.qsort Name.lt}"
  logInfo m!"JOINT_STRICT_LOGICAL_CLOSURE_PASS: {seen.toArray.size}; OPAQUE_VALUES_INSPECTED: {opaqueCount}; PROJECT_DECLARATIONS: {projectCount}"

end JointAudit
