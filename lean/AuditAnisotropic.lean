import IsingBulkAnisotropic
import Lean.Util.CollectAxioms

/-! Whole-candidate type/proof dependency and axiom checks. Run this strictly
on the frozen source-clean build; this is not a substitute for fresh kernel
replay or three independent whole-proof mathematical audits. -/
set_option maxHeartbeats 0

open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.Anisotropic.PhysicalField in
example {J lam : ℝ} (hJ : 0<J) (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL)
    (hG : PublishedRealGibbsFields J lam corrH corrL mH mL) :
    FullUniformFieldConclusion J lam corrH corrL mH mL :=
  full_uniform_field_conclusion hJ hlam hphys hG

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let endpoints := #[
    `IsingBulk.Anisotropic.full_uniform_field_conclusion,
    `IsingBulk.Anisotropic.full_physical_conclusion,
    `IsingBulk.Anisotropic.full_analytic_conclusion,
    `IsingBulk.Anisotropic.highNormalizedBulk_naturalBoundary,
    `IsingBulk.Anisotropic.lowNormalizedBulk_naturalBoundary,
    `IsingBulk.Anisotropic.highPhysicalBulk_naturalBoundary,
    `IsingBulk.Anisotropic.lowPhysicalBulk_naturalBoundary,
    `IsingBulk.Anisotropic.NegativeDominance.high_negative_prime_no_extension,
    `IsingBulk.Anisotropic.NegativeDominance.actual_negative_paper_radius_zero,
    `IsingBulk.Anisotropic.isotropic_full_physical_conclusion]
  for name in endpoints do
    let some info := env.checked.get.find? name
      | throwError "Missing ANISO endpoint: {name}"
    unless info.isTheorem do
      throwError "ANISO endpoint is not a theorem: {name}"
    logInfo m!"ANISO_ENDPOINT_TYPE: {name}; {info.type}"
    let axs ← Lean.collectAxioms name
    logInfo m!"ANISO_ENDPOINT_AXIOMS: {name}; {axs}"
    for ax in axs do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Unapproved endpoint axiom: {name}; {ax}"
  for name in #[
      `IsingBulk.Anisotropic.FullAnalyticConclusion,
      `IsingBulk.Anisotropic.FullPhysicalConclusion,
      `IsingBulk.Anisotropic.FullUniformFieldConclusion,
      `IsingBulk.Anisotropic.RealPhysicalIdentification,
      `IsingBulk.Anisotropic.RealUniformFieldIdentification,
      `IsingBulk.Anisotropic.FormFactors.PublishedRealSpinFormFactors,
      `IsingBulk.Anisotropic.PhysicalField.PublishedRealGibbsFields] do
    let some info := env.checked.get.find? name
      | throwError "Missing contract or physical interface: {name}"
    logInfo m!"ANISO_CONTRACT_TYPE: {name}; {info.type}"
    if let some value := info.value? true then
      logInfo m!"ANISO_CONTRACT_DEFINITION: {name}; {value}"
  let mut todo : List Name := [`IsingBulk.Anisotropic.full_uniform_field_conclusion]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | throwError "Missing compiled type/proof dependency: {name}"
    let typeDeps := info.type.getUsedConstants.toList
    let valueDeps := match info.value? true with
      | some value => value.getUsedConstants.toList
      | none => []
    todo := typeDeps ++ valueDeps ++ todo
    if let .inductInfo value := info then todo := value.ctors ++ todo
    if info.isUnsafe then throwError "Unsafe final type/proof dependency: {name}"
    if info.isAxiom then
      unless name == `propext || name == `Classical.choice || name == `Quot.sound do
        throwError "Unapproved final type/proof axiom: {name}"
    if (`IsingBulk).isPrefixOf name then
      logInfo m!"ANISO_DEPENDENCY_EDGE: {name}; TYPE: {typeDeps}; VALUE: {valueDeps}"
  for name in #[
      `IsingBulk.Anisotropic.NegativeDominance.high_negative_prime_no_extension,
      `IsingBulk.Anisotropic.NegativeDominance.actual_negative_paper_radius_zero,
      `IsingBulk.Anisotropic.NegativeDominance.exists_actual_middle_particle_bound,
      `IsingBulk.Anisotropic.NegativeDominance.actual_resonant_high_particle_bound,
      `IsingBulk.Anisotropic.NegativeDominance.negative_paper_ranges_of_particle_estimates,
      `IsingBulk.Anisotropic.NegativeDominance.physical_outer_jet_cauchy,
      `IsingBulk.Anisotropic.NegativeDominance.negative_paper_chart_no_extension,
      `IsingBulk.Anisotropic.NegativeCycles.physical_central_kernel_decomposition,
      `IsingBulk.Anisotropic.NegativeCycles.physical_resonant_residue_decomposition,
      `IsingBulk.Anisotropic.NegativeNormalForm.exists_actual_central_fixed_cutoff,
      `IsingBulk.Anisotropic.lowNormalizedBulk_naturalBoundary,
      `IsingBulk.Anisotropic.realUniformFieldIdentification_of_published] do
    unless seen.contains name do
      throwError "Missing actual full-chain dependency: {name}"
  logInfo m!"ANISO_FINAL_TYPE_PROOF_CLOSURE: {seen.toArray.size}"
  let projectModule := fun name : Name =>
    match env.getModuleIdxFor? name with
    | some idx => (`IsingBulk).isPrefixOf env.header.moduleNames[idx.toNat]!
    | none => false
  let entries := env.constants.toList.filter fun (name, _) => projectModule name
  let mut allTodo := entries.map Prod.fst
  let mut allSeen : NameSet := {}
  let mut allAxioms : NameSet := {}
  while !allTodo.isEmpty do
    let name := allTodo.head!
    allTodo := allTodo.tail!
    if allSeen.contains name then continue
    allSeen := allSeen.insert name
    let some info := env.checked.get.find? name
      | throwError "Missing whole-source dependency: {name}"
    if projectModule name && (info.isUnsafe || info.isAxiom) then
      throwError "Unsafe or axiomatic project declaration: {name}"
    if info.isAxiom then allAxioms := allAxioms.insert name
    allTodo := info.type.getUsedConstants.toList ++ allTodo
    if let some value := info.value? true then
      allTodo := value.getUsedConstants.toList ++ allTodo
    if let .inductInfo value := info then allTodo := value.ctors ++ allTodo
  for name in allAxioms do
    unless name == `propext || name == `Classical.choice || name == `Quot.sound do
      throwError "Unapproved whole-source axiom: {name}"
  logInfo m!"ANISO_ALL_SOURCE_AXIOMS: {allAxioms.toArray.qsort Name.lt}"
  logInfo m!"ANISO_STRICT_AUDIT_PASSED: {entries.length} project declarations; {allSeen.toArray.size} dependency constants"
