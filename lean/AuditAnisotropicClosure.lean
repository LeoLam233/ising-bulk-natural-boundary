import IsingBulkAnisotropic
import Lean.Util.CollectAxioms

#print IsingBulk.Anisotropic.FormFactors.PublishedRealSpinFormFactors
#print IsingBulk.Anisotropic.PhysicalField.PublishedRealGibbsFields
#print IsingBulk.Anisotropic.PhysicalField.GibbsFieldConditions
#print IsingBulk.Anisotropic.HasDomainExtension
#print IsingBulk.Anisotropic.NaturalBoundaryOn

/-! Publication-only audit. The C001 source and original AuditAnisotropic are
unchanged. Traverse checked declaration types and proof/definition values,
including constructors, rather than treating `#print axioms` as a premise audit. -/
open Lean in
run_cmd do
  let env ← getEnv
  let endpoint := `IsingBulk.Anisotropic.full_uniform_field_conclusion
  let some finalInfo := env.checked.get.find? endpoint
    | throwError "Missing final ANISO theorem"
  unless finalInfo.isTheorem do throwError "Final ANISO endpoint is not a theorem"
  logInfo m!"ANISO_PUBLICATION_TERMINAL_TYPE: {finalInfo.type}"
  let approved := fun n : Name =>
    n == `propext || n == `Classical.choice || n == `Quot.sound
  let mut todo : List Name := [endpoint]
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | throwError "Missing checked dependency: {name}"
    if info.isPartial then throwError "Partial final type/proof dependency: {name}"
    if info.isUnsafe then throwError "Unsafe final type/proof dependency: {name}"
    if name == `sorryAx then throwError "sorryAx in final type/proof closure"
    if info.isAxiom then
      unless approved name do throwError "Unexpected final axiom: {name}"
      axioms := axioms.insert name
    todo := info.type.getUsedConstants.toList ++ todo
    if let some value := info.value? true then
      todo := value.getUsedConstants.toList ++ todo
    if let .inductInfo value := info then todo := value.ctors ++ todo
  for required in #[
      `IsingBulk.Anisotropic.FormFactors.PublishedRealSpinFormFactors,
      `IsingBulk.Anisotropic.PhysicalField.PublishedRealGibbsFields,
      `IsingBulk.Anisotropic.RealPhysicalIdentification,
      `IsingBulk.Anisotropic.RealUniformFieldIdentification,
      `IsingBulk.Anisotropic.HasDomainExtension,
      `IsingBulk.Anisotropic.NaturalBoundaryOn,
      `IsingBulk.HT.Final.interiorFullBulk_unit_circle_no_extension,
      `IsingBulk.Final.theorem_nb,
      `IsingBulk.Anisotropic.NegativeDominance.high_negative_prime_no_extension,
      `IsingBulk.Anisotropic.lowNormalizedBulk_naturalBoundary] do
    unless seen.contains required do
      throwError "Missing required final dependency: {required}"
    logInfo m!"ANISO_PUBLICATION_REQUIRED_DEPENDENCY: {required}"
  let projectModule := fun name : Name =>
    match env.getModuleIdxFor? name with
    | some idx => (`IsingBulk).isPrefixOf env.header.moduleNames[idx.toNat]!
    | none => false
  let mut partials : Array Name := #[]
  for (name, info) in env.constants.toList do
    if projectModule name && info.isPartial then
      if seen.contains name then throwError "Project partial helper in theorem closure: {name}"
      partials := partials.push name
  unless partials.size == 30 do
    throwError "Expected 30 frozen compiler partial execution helpers; found {partials.size}"
  for name in partials.qsort Name.lt do
    logInfo m!"ANISO_PARTIAL_EXECUTION_HELPER_OUTSIDE_CLOSURE: {name}"
  logInfo m!"ANISO_FINAL_CLOSURE_AXIOMS: {axioms.toArray.qsort Name.lt}"
  logInfo m!"ANISO_FINAL_CLOSURE_PASSED: {seen.toArray.size} constants; zero partial/unsafe/sorry; {partials.size} project partial helpers outside closure"
