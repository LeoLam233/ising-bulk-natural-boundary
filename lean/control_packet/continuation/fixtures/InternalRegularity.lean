import IsingBulk

/- Exact no-E3 applications and a traversal of compiled types AND proof bodies.
An axiom-only audit cannot detect an explicit theorem parameter such as E3. -/
open IsingBulk.First IsingBulk.Final IsingBulk.Tail

example : ∀ z : ℂ, ‖z‖ = 1 → ¬ HasExteriorExtension exteriorNormalizedBulk z := theorem_nb

example {J : ℝ} (hJ : 0 < J) {chi : ℂ → ℂ} {M : ℝ → ℂ}
    (hE1 : PhysicalSusceptibilityE1 J chi M) (hE2 : YangMagnetizationE2 M) :
    AnalyticOnNhd ℂ (rightPhysicalBulk J) {s : ℂ | 1 < ‖s‖ ∧ 0 < s.re} ∧
      (∀ x : ℝ, 16 < x → chi (x:ℂ) = rightPhysicalBulk J (x:ℂ)) ∧
      (∀ z : ℂ, ‖z‖ = 1 → ¬ HasPhysicalBoundaryExtension J exteriorNormalizedBulk z) :=
  theorem_nb_physical hJ hE1 hE2

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden := #[`IsingBulk.First.PublishedTWFixedOrderInput,
    `IsingBulk.First.PublishedFullSiteBounded,
    `IsingBulk.First.selected_lower_fullSite_bounded,
    `IsingBulk.First.lowerOrder_radial_bound_of_published,
    `IsingBulk.First.lowerOrder_fixed_radius_bound_of_published]
  let required := #[`IsingBulk.First.nonNickel_active_separated,
    `IsingBulk.First.nonNickel_fixed_radius_radial_bound,
    `IsingBulk.First.source_complement_global_bound]
  for endpoint in #[`IsingBulk.First.theorem_first, `IsingBulk.Final.theorem_nb,
      `IsingBulk.Final.theorem_nb_physical] do
    let mut todo : List Name := [endpoint]
    let mut seen : NameSet := {}
    while !todo.isEmpty do
      let name := todo.head!
      todo := todo.tail!
      if seen.contains name then continue
      seen := seen.insert name
      if forbidden.contains name then
        throwError "E3 is transitively reachable from {endpoint}: {name}"
      let some info := env.checked.get.find? name
        | throwError "Missing compiled dependency: {name}"
      todo := info.type.getUsedConstants.toList ++ todo
      if let some value := info.value? true then
        todo := value.getUsedConstants.toList ++ todo
      if let .inductInfo value := info then
        todo := value.ctors ++ todo
    for name in required do
      unless seen.contains name do
        throwError "Internal analytic replacement is not reachable from {endpoint}: {name}"
    logInfo m!"NO_E3_TRANSITIVE: {endpoint}; CONSTANTS: {seen.toArray.size}; INTERNAL_REPLACEMENT_REACHABLE"
  logInfo "INTERNAL_REGULARITY_DEPENDENCY_CONTROL_PASSED"
