import IsingBulk.Joint.Isotropic.BoundaryFromSlices
import IsingBulk.Joint.Isotropic.UnitDomainCollars

namespace IsingBulk.Joint
noncomputable section
open Set IsingBulk.Anisotropic

/-- The full reduced HT descendant, derived through R, in the ordinary
componentwise holomorphic sense at every unit-circle point. -/
theorem high_descendant_componentwise
    {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) :
    HolomorphicNaturalBoundaryOn {s : ℂ | ‖s‖ < 1} IsingBulk.HT.Final.interiorFullBulk := by
  refine ⟨IsingBulk.HT.Final.interiorFullBulk_analyticOn.differentiableOn,?_⟩
  intro s hs he
  have hn : ‖s‖ = 1 := frontier_lt_subset_eq continuous_norm continuous_const hs
  exact high_descendant_no_extension_from_R hphys hn (scalar_fullExtension_of_holomorphic
    (holomorphicFullExtension_of_component disk_hasLocalCollar hs he))

/-- The full connected LT descendant; no exterior inverse temperature is
introduced. Its covering and deck invariance are proved in separate declarations. -/
theorem low_descendant_componentwise
    {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) :
    HolomorphicNaturalBoundaryOn {s : ℂ | 1 < ‖s‖} IsingBulk.Tail.exteriorNormalizedBulk := by
  refine ⟨IsingBulk.Tail.exteriorNormalizedBulk_analyticOn.differentiableOn,?_⟩
  intro s hs he
  have hn : ‖s‖ = 1 := (frontier_lt_subset_eq continuous_const continuous_norm hs).symm
  exact low_descendant_no_extension_from_R hphys hn (scalar_fullExtension_of_holomorphic
    (holomorphicFullExtension_of_component exterior_hasLocalCollar hs he))

/-- Exact isotropic geometry, actual normalized descent, and both entire-circle
obstructions, bundled without identifying the distinct odd/even physical germs. -/
theorem isotropic_complete_descendants
    {corrH corrL : PhysicalField.CorrelationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL) :
    Set.BijOn Complex.sinh (omegaH 1) {s : ℂ | ‖s‖ < 1} ∧
    IsCoveringMap lowSinhMap ∧ IsSimplyConnected (omegaL 1) ∧
    (∀ z ∈ omegaH 1, FormFactors.highNormalizedBulk (ratioSlice 1 z) =
      IsingBulk.HT.Final.interiorFullBulk (Complex.sinh z)) ∧
    (∀ z ∈ omegaL 1, FormFactors.lowNormalizedBulk (ratioSlice 1 z) =
      IsingBulk.Tail.exteriorNormalizedBulk (Complex.sinh z)) ∧
    IsingBulk.HT.Final.interiorFullBulk 0 = 1 ∧
    HolomorphicNaturalBoundaryOn {s : ℂ | ‖s‖ < 1} IsingBulk.HT.Final.interiorFullBulk ∧
    HolomorphicNaturalBoundaryOn {s : ℂ | 1 < ‖s‖} IsingBulk.Tail.exteriorNormalizedBulk :=
  ⟨sinh_bijOn_high,low_universal_covering.1,low_universal_covering.2,
    fun _ hz => joint_high_isotropic_identity hz,
    fun _ hz => joint_low_isotropic_identity (hphys 1 (by norm_num)) hz,
    high_descendant_zero,high_descendant_componentwise hphys,low_descendant_componentwise hphys⟩

end
end IsingBulk.Joint
