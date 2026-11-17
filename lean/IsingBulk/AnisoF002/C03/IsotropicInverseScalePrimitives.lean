import IsingBulk.AnisoF002.C03.IsotropicActualPopulationScales
import IsingBulk.AnisoF002.C03.IsotropicOneSidedImage

/-!
# Actual inverse slopes and bounded regular denominators on the full arc

The bounds come from the same explicit inverse that equals every
actual deformed angle. They include the entire one-sided arc and are
uniform in particle count and all full population fractions.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def explicitRightCoordinateSlope (q : ℂ × ℂ) : ℂ :=
  Complex.sin (q.2 - explicitRightInverse q) / explicitRightDenominator q

theorem explicitRightCoordinateSlope_analyticAt (q : ℂ × ℂ)
    (hU : AnalyticAt ℂ explicitRightInverse q) (hD : explicitRightDenominator q ≠ 0) :
    AnalyticAt ℂ explicitRightCoordinateSlope q :=
  (Complex.analyticAt_sin.comp (analyticAt_snd.sub hU)).div
    (explicitRightDenominator_analyticAt q hU) hD

theorem explicitRightCoordinateSlope_eq_deriv (q : ℂ × ℂ)
    (hU : AnalyticAt ℂ explicitRightInverse q) (hc : Complex.cos (q.2 / 2) ≠ 0)
    (hD : explicitRightDenominator q ≠ 0) :
    explicitRightCoordinateSlope q = deriv (fun z => explicitRightInverse (q.1, z)) q.2 :=
  (joint_inverse_coordinate_derivative explicitRightInverse q.1 q.2 hU
    (explicitRightInverse_dispersion_eventually q hc) hD).deriv.symm

theorem exists_oneSided_inverse_slope_bounds (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      ∀ q ∈ cthickening r (oneSidedParameterArc S),
        AnalyticAt ℂ explicitRightInverse q ∧ Complex.cos (q.2 / 2) ≠ 0 ∧
        explicitRightDenominator q ≠ 0 ∧
        ‖deriv (fun z => explicitRightInverse (q.1, z)) q.2‖ ≤ C ∧
        ‖(explicitRightDenominator q)⁻¹‖ ≤ C := by
  obtain ⟨r, hr, hU, hdata, _⟩ := exists_oneSided_inverse_protected_neighborhood S hS
  have hslope : AnalyticOnNhd ℂ explicitRightCoordinateSlope
      (cthickening r (oneSidedParameterArc S)) :=
    fun q hq => explicitRightCoordinateSlope_analyticAt q (hU q hq) (hdata q hq).2.2
  have hinv : AnalyticOnNhd ℂ (fun q => (explicitRightDenominator q)⁻¹)
      (cthickening r (oneSidedParameterArc S)) :=
    fun q hq => (explicitRightDenominator_analyticAt q (hU q hq)).inv (hdata q hq).2.2
  obtain ⟨C₁, hC₁⟩ := (oneSidedParameterArc_isCompact S hS.1).cthickening.exists_bound_of_continuousOn
    hslope.continuousOn
  obtain ⟨C₂, hC₂⟩ := (oneSidedParameterArc_isCompact S hS.1).cthickening.exists_bound_of_continuousOn
    hinv.continuousOn
  let C := max 1 (max C₁ C₂)
  refine ⟨r, C, hr, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q hq
  have hd := hdata q hq
  refine ⟨hU q hq, hd.2.1, hd.2.2, ?_, (hC₂ q hq).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  rw [← explicitRightCoordinateSlope_eq_deriv q (hU q hq) hd.2.1 hd.2.2]
  exact (hC₁ q hq).trans ((le_max_left _ _).trans (le_max_right _ _))

theorem oneSidedProductDomain_single_mem {N : ℕ} {S r : ℝ} {q : ℂ × (Fin N → ℂ)}
    (hq : q ∈ oneSidedProductDomain S r N) (i : Fin N) :
    (q.1, q.2 i) ∈ thickening r (oneSidedParameterArc S) := by
  obtain ⟨v, hv, hd⟩ := mem_thickening_iff.mp (hq.2 i)
  apply mem_thickening_iff.mpr
  refine ⟨((S : ℂ), v), ⟨rfl, hv⟩, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  exact ⟨hq.1, hd⟩

theorem exists_actual_oneSided_inverse_slope_bounds (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ s : ℂ, 0 < s.im → dist s (S : ℂ) < δ →
      ∀ η τ ξ : ℝ, 0 < η → τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-Real.pi - δ) δ) →
      ∀ i : Fin N,
        let v := (actualHomotopyRegularTuple s η τ ξ θ).2 i
        AnalyticAt ℂ explicitRightInverse (s, v) ∧ Complex.cos (v / 2) ≠ 0 ∧
        explicitRightDenominator (s, v) ≠ 0 ∧
        explicitRightInverse (s, v) = actualHomotopyAngle η τ ξ θ i ∧
        ‖deriv (fun z => explicitRightInverse (s, z)) v‖ ≤ C ∧
        ‖(explicitRightDenominator (s, v))⁻¹‖ ≤ C := by
  obtain ⟨r, C, hr, hC, hbound⟩ := exists_oneSided_inverse_slope_bounds S hS
  obtain ⟨δ, hδ, hdom⟩ := exists_actual_oneSided_homotopy_domain S r hS hr
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro N hN s hs hsnear η τ ξ hη hτ hξ θ hθ i
  obtain ⟨hin, heq⟩ := hdom N hN s hs hsnear η τ ξ hη hτ hξ θ hθ
  have hq := thickening_subset_cthickening r _ (oneSidedProductDomain_single_mem hin i)
  have hh := hbound _ hq
  exact ⟨hh.1, hh.2.1, hh.2.2.1, heq i, hh.2.2.2⟩

end IsingBulk.AnisoF002.Isotropic
