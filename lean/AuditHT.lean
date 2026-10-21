import IsingBulkHT
import Lean.Util.CollectAxioms

/-! Compiled HT audit, separate from the protected LT audit. Importing this
file compiles the complete HT root, not just a convenient endpoint closure.
These checks are not a replacement for fresh official kernel replay or the
three independent final adversarial audit rounds. -/

open IsingBulk.HT.Final IsingBulk.Final in
example : ∀ z : ℂ, ‖z‖ = 1 → ¬ HasExteriorExtension exteriorOddSeries z :=
  exteriorOddSeries_unit_circle_no_extension

open IsingBulk.HT.Final in
example {J : ℝ} (hJ : 0 < J) :
    AnalyticOnNhd ℂ (interiorPhysicalSusceptibility J) {s : ℂ | ‖s‖ < 1} ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ¬ HasInteriorExtension (interiorPhysicalSusceptibility J) z :=
  interiorPhysicalSusceptibility_natural_boundary hJ

open IsingBulk.HT.Final in
example {J : ℝ} (hJ : 0 < J) {chi : ℂ → ℂ}
    (hrep : PhysicalSusceptibilityRepresentation J chi) :
    AnalyticOnNhd ℂ (interiorPhysicalSusceptibility J) {s : ℂ | ‖s‖ < 1} ∧
      (∀ x : ℝ, 0 < x → x < 1/16 →
        chi (x:ℂ) = interiorPhysicalSusceptibility J (x:ℂ)) ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ¬ HasInteriorExtension (interiorPhysicalSusceptibility J) z :=
  physicalSusceptibility_germ_natural_boundary hJ hrep

open IsingBulk.HT.Final in
example {J : ℝ} (hJ : 0 < J) {chi : ℂ → ℂ}
    (hchi : AnalyticOnNhd ℂ chi {s : ℂ | ‖s‖ < 1})
    (hrep : PhysicalSusceptibilityRepresentation J chi) :
    ∀ z : ℂ, ‖z‖ = 1 → ¬ HasInteriorExtension chi z :=
  physicalSusceptibility_unit_circle_no_extension hJ hchi hrep

open IsingBulk.HT.Final in
example {J : ℝ} (hJ : 0 < J) {chi : ℂ → ℂ}
    (hpub : PublishedAngularSusceptibilityRepresentation J chi) :
    AnalyticOnNhd ℂ (interiorPhysicalSusceptibility J) {s : ℂ | ‖s‖ < 1} ∧
      (∀ x : ℝ, 0 < x → x < 1 →
        chi (x:ℂ) = interiorPhysicalSusceptibility J (x:ℂ)) ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ¬ HasInteriorExtension (interiorPhysicalSusceptibility J) z :=
  publishedPhysicalSusceptibility_germ_natural_boundary hJ hpub

/- The exact published representation predicate has an explicit witness.
This is a source identity for the independently constructed analytic germ,
not an assumption about the physical observable. -/
open IsingBulk.HT.Final in
example {J : ℝ} (hJ : 0 < J) :
    ∃ chi : ℂ → ℂ, PublishedAngularSusceptibilityRepresentation J chi :=
  ⟨interiorPhysicalSusceptibility J,
    interiorPhysicalSusceptibility_publishedAngularRepresentation hJ⟩

/- Negative controls: the extension predicates admit ordinary entire
functions. A boundary obstruction cannot follow from the predicate being
false for every function or from a missing extension witness. -/
open IsingBulk.HT.Final in
example (z : ℂ) : HasInteriorExtension (fun _ : ℂ => (0:ℂ)) z := by
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ z,(fun _ => 0),?_,?_⟩
  · intro _ _
    exact analyticAt_const
  · intro _ _
    rfl

open IsingBulk.Final in
example (z : ℂ) : HasExteriorExtension (fun _ : ℂ => (0:ℂ)) z := by
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ z,(fun _ => 0),?_,?_⟩
  · intro _ _
    exact analyticAt_const
  · intro _ _
    rfl

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let endpointNames := #[
    `IsingBulk.HT.First.first_standard_odd_source_asymptotic,
    `IsingBulk.HT.First.first_standard_odd_source_closed_asymptotic,
    `IsingBulk.HT.First.first_standard_odd_source_closed_and_sharp,
    `IsingBulk.HT.First.first_standard_odd_source_lower_littleO,
    `IsingBulk.HT.First.first_standard_odd_source_sharp_lower_bounds,
    `IsingBulk.HT.First.Regular.negative_first_standard_odd_source_asymptotic,
    `IsingBulk.HT.First.Regular.negative_first_standard_odd_source_closed_asymptotic,
    `IsingBulk.HT.First.Regular.negative_first_standard_odd_source_closed_and_sharp,
    `IsingBulk.HT.First.Regular.negative_first_standard_odd_source_lower_littleO,
    `IsingBulk.HT.First.Regular.negative_first_standard_odd_source_sharp_lower_bounds,
    `IsingBulk.HT.Tail.actual_upper_full_odd_tail_summable,
    `IsingBulk.HT.Tail.selected_positive_absolute_upper_full_odd_tail_small,
    `IsingBulk.HT.Tail.negative_original_family_absolute_upper_full_odd_tail_small,
    `IsingBulk.HT.Final.exteriorOddSeries_iteratedDeriv,
    `IsingBulk.HT.Final.selected_positive_exterior_full_limit,
    `IsingBulk.HT.Final.selected_negative_exterior_full_limit,
    `IsingBulk.HT.Final.exteriorOddSeries_unit_circle_no_extension,
    `IsingBulk.HT.Final.interiorFullBulk_unit_circle_no_extension,
    `IsingBulk.HT.Final.interiorPhysicalSusceptibility_natural_boundary,
    `IsingBulk.HT.Final.physicalSusceptibility_germ_natural_boundary,
    `IsingBulk.HT.Final.physicalSusceptibility_unit_circle_no_extension,
    `IsingBulk.HT.Final.publishedPhysicalSusceptibility_germ_natural_boundary,
    `IsingBulk.HT.Final.publishedPhysicalSusceptibility_unit_circle_no_extension,
    `IsingBulk.HT.Final.interiorFullBulk_publishedAngularRepresentation,
    `IsingBulk.HT.Final.interiorPhysicalSusceptibility_publishedAngularRepresentation,
    `IsingBulk.HT.Final.publishedAngularBulk_to_contour,
    `IsingBulk.HT.Contour.physicalLatticeCoefficient_eq_unit_contour,
    `IsingBulk.HT.Contour.physicalLatticeCoefficient_onsite_eq_formFactor,
    `IsingBulk.HT.Contour.physicalLatticeCoefficient_eq_double_contour,
    `IsingBulk.HT.Contour.physicalLatticeCoefficient_horizontal_reflection,
    `IsingBulk.HT.Contour.physicalFullLatticeCoefficient_summable_eq_standardFormFactor,
    `IsingBulk.HT.Contour.physicalLatticeCoefficient_horizontal_tsum,
    `IsingBulk.HT.Contour.physicalAngularCoefficient_eq_fullLattice_tsum,
    `IsingBulk.HT.Contour.physicalAngularCoefficient_eq_standardFormFactor,
    `IsingBulk.HT.Final.physicalFullLatticeOddSeries_eq_fixedOddFullSeries,
    `IsingBulk.HT.Final.physicalFullLattice_odd_norm_summable]
  for name in endpointNames do
    let some info := env.checked.get.find? name
      | throwError "Missing HT endpoint: {name}"
    unless info.isTheorem do
      throwError "HT endpoint is not a theorem: {name}"
    logInfo m!"HT_ENDPOINT_TYPE: {name}; {info.type}"
    let axs ← Lean.collectAxioms name
    logInfo m!"HT_ENDPOINT_AXIOMS: {name}; {axs}"
  for name in #[`IsingBulk.HT.Final.RealFullBulkRepresentation,
      `IsingBulk.HT.Final.PhysicalSusceptibilityRepresentation,
      `IsingBulk.HT.Final.PublishedAngularBulkRepresentation,
      `IsingBulk.HT.Final.PublishedAngularSusceptibilityRepresentation] do
    let some info := env.checked.get.find? name
      | throwError "Missing physical identification interface: {name}"
    logInfo m!"EXPLICIT_PHYSICAL_INTERFACE_TYPE: {name}; {info.type}"
    if let some value := info.value? true then
      logInfo m!"EXPLICIT_PHYSICAL_INTERFACE_DEFINITION: {name}; {value}"
  let forbidden := #[
    `IsingBulk.First.PublishedTWFixedOrderInput,
    `IsingBulk.First.PublishedFullSiteBounded,
    `IsingBulk.Final.RealFredholmE1,
    `IsingBulk.Final.YangMagnetizationE2,
    `IsingBulk.Final.theorem_nb,
    `IsingBulk.Final.theorem_nb_physical,
    `IsingBulk.HT.Final.RealFullBulkRepresentation,
    `IsingBulk.HT.Final.PhysicalSusceptibilityRepresentation,
    `IsingBulk.HT.Final.PublishedAngularBulkRepresentation,
    `IsingBulk.HT.Final.PublishedAngularSusceptibilityRepresentation]
  let required := #[
    `IsingBulk.First.standardFormFactor,
    `IsingBulk.HT.First.first_standard_odd_source_asymptotic,
    `IsingBulk.HT.First.Regular.negative_first_standard_odd_source_asymptotic,
    `IsingBulk.HT.Tail.selected_positive_absolute_upper_full_odd_tail_small,
    `IsingBulk.HT.Tail.negative_original_family_absolute_upper_full_odd_tail_small]
  for endpoint in #[
      `IsingBulk.HT.Final.exteriorOddSeries_unit_circle_no_extension,
      `IsingBulk.HT.Final.interiorPhysicalSusceptibility_natural_boundary] do
    let mut todo : List Name := [endpoint]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if seen.contains name then continue
      seen := seen.insert name
      if forbidden.contains name then
        throwError "Forbidden physics/E3/LT conclusion in HT analytic proof: {endpoint}; {name}"
      let some info := env.checked.get.find? name
        | throwError "Missing compiled dependency: {name}"
      todo := info.type.getUsedConstants.toList ++ todo
      if let some value := info.value? true then
        todo := value.getUsedConstants.toList ++ todo
      if let .inductInfo value := info then
        todo := value.ctors ++ todo
    for name in required do
      unless seen.contains name do
        throwError "Missing actual HT FIRST/TAIL/source dependency: {endpoint}; {name}"
    logInfo m!"HT_ANALYTIC_DEPENDENCY_CONTROL: {endpoint}; CONSTANTS: {seen.toArray.size}"
  let physicalEndpoint :=
    `IsingBulk.HT.Final.publishedPhysicalSusceptibility_germ_natural_boundary
  let physicalRequired := required ++ #[
    `IsingBulk.HT.Final.PublishedAngularSusceptibilityRepresentation,
    `IsingBulk.HT.Final.publishedAngularBulk_to_contour,
    `IsingBulk.HT.Contour.physicalAngularCoefficient_eq_standardFormFactor,
    `IsingBulk.HT.Contour.physicalAngularCoefficient_eq_fullLattice_tsum,
    `IsingBulk.HT.Contour.physicalLatticeCoefficient_horizontal_tsum,
    `IsingBulk.HT.Contour.torus_exponential_coefficient,
    `IsingBulk.HT.Contour.physicalConstrainedVerticalCoefficient_summable_eq_angular,
    `IsingBulk.HT.Contour.physicalFullLatticeCoefficient_summable_eq_standardFormFactor]
  let physicalForbidden := #[
    `IsingBulk.First.PublishedTWFixedOrderInput,
    `IsingBulk.First.PublishedFullSiteBounded,
    `IsingBulk.Final.RealFredholmE1,
    `IsingBulk.Final.YangMagnetizationE2,
    `IsingBulk.Final.theorem_nb,
    `IsingBulk.Final.theorem_nb_physical]
  let mut physicalTodo : List Name := [physicalEndpoint]
  let mut physicalSeen : NameSet := {}
  while !physicalTodo.isEmpty do
    let name := physicalTodo.head!
    physicalTodo := physicalTodo.tail!
    if physicalSeen.contains name then continue
    physicalSeen := physicalSeen.insert name
    if physicalForbidden.contains name then
      throwError "Forbidden LT physics/E3/conclusion in physical HT theorem: {name}"
    let some info := env.checked.get.find? name
      | throwError "Missing compiled physical dependency: {name}"
    physicalTodo := info.type.getUsedConstants.toList ++ physicalTodo
    if let some value := info.value? true then
      physicalTodo := value.getUsedConstants.toList ++ physicalTodo
    if let .inductInfo value := info then
      physicalTodo := value.ctors ++ physicalTodo
  for name in physicalRequired do
    unless physicalSeen.contains name do
      throwError "Missing actual Fourier/lattice/FIRST/TAIL dependency in physical HT theorem: {name}"
  logInfo m!"HT_PHYSICAL_DEPENDENCY_CONTROL: {physicalEndpoint}; CONSTANTS: {physicalSeen.toArray.size}"
  let projectModule := fun name : Name =>
    match env.getModuleIdxFor? name with
    | some idx => (`IsingBulk).isPrefixOf env.header.moduleNames[idx.toNat]!
    | none => false
  let entries := env.constants.toList.filter fun (name, _) => projectModule name
  for (name, info) in entries do
    if info.isTheorem && info.isUnsafe then
      throwError "Unexpected unsafe project theorem: {name}"
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
  logInfo m!"HT AXIOM UNION: {axioms.toArray.qsort Name.lt}"
  logInfo m!"HT AUDIT PASSED: {names.length} kernel-safe project declarations"
