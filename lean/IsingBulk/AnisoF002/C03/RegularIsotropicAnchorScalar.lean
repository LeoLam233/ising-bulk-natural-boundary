import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorField
import IsingBulk.AnisoF002.C03.RegularIsotropicExteriorGap
import IsingBulk.AnisoF002.C03.IsotropicFullCircleOneBody
import IsingBulk.AnisoF002.C03.IsotropicOneSidedRetainedJets

/-!
# Uniform scalar data for the anchored regular-coordinate transport

The actual root has a holomorphic expression in the regular coordinates.
The entire one-sided compact arc supplies common slope and Lipschitz
bounds. A single exterior physical root quantitatively protects the
named inverse-coordinate slope.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter Metric

def regularInverseRoot (q : ℂ × ℂ) : ℂ :=
  Complex.exp (-((q.2 - explicitRightInverse q) * Complex.I))

theorem regularInverseRoot_analyticAt (q : ℂ × ℂ)
    (hU : AnalyticAt ℂ explicitRightInverse q) : AnalyticAt ℂ regularInverseRoot q :=
  analyticAt_cexp.comp (((analyticAt_snd.sub hU).mul analyticAt_const).neg)

theorem regularInverseRoot_actual {N : ℕ} (η τ ξ : ℝ)
    (q : ℂ × (Fin N → ℝ)) (i : Fin N)
    (hU : explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
      actualHomotopyAngle η τ ξ q.2 i) :
    regularInverseRoot (q.1, actualPhysicalCoordinate η τ ξ i q) =
      isotropicInteriorRoot (q.1, actualHomotopyAngle η τ ξ q.2 i) := by
  unfold regularInverseRoot
  rw [hU]
  have he : actualPhysicalCoordinate η τ ξ i q - actualHomotopyAngle η τ ξ q.2 i =
      upperPhysicalPhase (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)) := by
    simp only [actualPhysicalCoordinate, physicalRegularCoordinate, add_sub_cancel_left]
  rw [he]
  exact upperPhysicalPhase_exp _

/-- These constants are fixed before the population and the anchor. -/
theorem exists_oneSided_scalar_transport_control (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r C : ℝ, 0 < r ∧ 1 ≤ C ∧
      ∀ q ∈ cthickening r (oneSidedParameterArc S),
        AnalyticAt ℂ explicitRightInverse q ∧
        AnalyticAt ℂ regularInverseRoot q ∧
        AnalyticAt ℂ (jointCoordinateDerivative explicitRightInverse) q ∧
        ‖fderiv ℂ explicitRightInverse q‖ ≤ C ∧
        ‖fderiv ℂ regularInverseRoot q‖ ≤ C ∧
        ‖fderiv ℂ (jointCoordinateDerivative explicitRightInverse) q‖ ≤ C := by
  obtain ⟨r, hr, hU, _, hjets⟩ := exists_oneSided_inverse_protected_neighborhood S hS
  have hR : AnalyticOnNhd ℂ regularInverseRoot (cthickening r (oneSidedParameterArc S)) :=
    fun q hq => regularInverseRoot_analyticAt q (hU q hq)
  have hv : AnalyticOnNhd ℂ (jointCoordinateDerivative explicitRightInverse)
      (cthickening r (oneSidedParameterArc S)) :=
    fun q hq => jointCoordinateDerivative_analyticAt _ q (hU q hq)
  have hcompact := (oneSidedParameterArc_isCompact S hS.1).cthickening (r := r)
  obtain ⟨CU, hCU⟩ := hjets 1
  obtain ⟨CR, hCR⟩ := hcompact.exists_bound_of_continuousOn (hR.fderiv).continuousOn
  obtain ⟨Cv, hCv⟩ := hcompact.exists_bound_of_continuousOn (hv.fderiv).continuousOn
  let C := max 1 (max CU (max CR Cv))
  refine ⟨r, C, hr, le_max_left _ _, ?_⟩
  intro q hq
  refine ⟨hU q hq, hR q hq, hv q hq, ?_, ?_, ?_⟩
  · have hu := hCU q hq
    rw [norm_iteratedFDeriv_one] at hu
    exact hu.trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hCR q hq).trans ((le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  · exact (hCv q hq).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))

theorem oneSidedScalar_half_ball_subset {S r : ℝ} {q : ℂ × ℂ}
    (hq : q ∈ thickening (r / 2) (oneSidedParameterArc S)) :
    ball q (r / 2) ⊆ cthickening r (oneSidedParameterArc S) := by
  intro p hp
  obtain ⟨a, ha, hqa⟩ := mem_thickening_iff.mp hq
  apply thickening_subset_cthickening r _
  apply mem_thickening_iff.mpr
  refine ⟨a, ha, (dist_triangle p q a).trans_lt ?_⟩
  have hpq : dist p q < r / 2 := hp
  linarith

theorem oneSidedScalar_lipschitz {S r C : ℝ} (hr : 0 < r)
    (f : ℂ × ℂ → ℂ)
    (hf : ∀ p ∈ cthickening r (oneSidedParameterArc S), DifferentiableAt ℂ f p)
    (hC : ∀ p ∈ cthickening r (oneSidedParameterArc S), ‖fderiv ℂ f p‖ ≤ C)
    (q : ℂ × ℂ) (hq : q ∈ thickening (r / 2) (oneSidedParameterArc S))
    (p : ℂ × ℂ) (hp : p ∈ ball q (r / 2)) :
    ‖f p - f q‖ ≤ C * ‖p - q‖ := by
  have hsub := oneSidedScalar_half_ball_subset hq
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => hf z (hsub hz)) (fun z hz => hC z (hsub hz))
    (convex_ball q (r / 2)) (mem_ball_self (half_pos hr)) hp

theorem root_oneBody_bound_of_norm_gap {r : ℂ} {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hr : ‖r‖ ≤ q) :
    ‖2 * r / (1 - r ^ 2)‖ ≤ 2 / (1 - q ^ 2) := by
  have hden : 0 < 1 - q ^ 2 := by nlinarith
  have hlo : 1 - q ^ 2 ≤ ‖1 - r ^ 2‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (r ^ 2)
    rw [norm_one, norm_pow] at hh
    have hp : ‖r‖ ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hr 2
    linarith
  rw [norm_div, norm_mul, Complex.norm_two]
  exact div_le_div₀ (by norm_num) (by nlinarith only [hr, hq1]) hden hlo

/-- The inverse-coordinate slope is bounded below using the actual
physical root gap, rather than assuming an additional regularity premise. -/
theorem actual_anchor_inverse_slope_lower {N : ℕ} (a : Fin N) (η τ ξ : ℝ)
    (x : ℂ × (Fin N → ℝ)) (q H : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) (hH : 0 ≤ H)
    (hW : 0 < (isotropicDispersion (x.1, actualHomotopyAngle η τ ξ x.2 a)).im)
    (hU : AnalyticAt ℂ explicitRightInverse (x.1, actualPhysicalCoordinate η τ ξ a x))
    (hc : Complex.cos (actualPhysicalCoordinate η τ ξ a x / 2) ≠ 0)
    (hD : explicitRightDenominator (x.1, actualPhysicalCoordinate η τ ξ a x) ≠ 0)
    (heq : explicitRightInverse (x.1, actualPhysicalCoordinate η τ ξ a x) =
      actualHomotopyAngle η τ ξ x.2 a)
    (hroot : ‖isotropicInteriorRoot (x.1, actualHomotopyAngle η τ ξ x.2 a)‖ ≤ q)
    (hsin : ‖Complex.sin (actualHomotopyAngle η τ ξ x.2 a)‖ ≤ H) :
    1 / (1 + H * (2 / (1 - q ^ 2))) ≤
      ‖jointCoordinateDerivative explicitRightInverse (x.1, actualPhysicalCoordinate η τ ξ a x)‖ := by
  have hden : 0 < 1 - q ^ 2 := by nlinarith
  have hC : 0 < 1 + H * (2 / (1 - q ^ 2)) := by positivity
  have hbody := root_oneBody_bound_of_norm_gap hq hq1 hroot
  rw [isotropic_oneBody_norm] at hbody
  have hmult : ‖actualCoordinateMultiplier η τ ξ x a‖ ≤ 1 + H * (2 / (1 - q ^ 2)) := by
    unfold actualCoordinateMultiplier
    calc
      _ ≤ 1 + ‖Complex.sin (actualHomotopyAngle η τ ξ x.2 a)‖ *
          ‖Complex.sin (actualPhysicalPhase η τ ξ x a)‖⁻¹ := by
        simpa only [norm_one, norm_div, div_eq_mul_inv, norm_mul, norm_inv] using norm_sub_le (1 : ℂ)
          (Complex.sin (actualHomotopyAngle η τ ξ x.2 a) / Complex.sin (actualPhysicalPhase η τ ξ x a))
      _ ≤ _ := add_le_add le_rfl (mul_le_mul hsin hbody (inv_nonneg.mpr (norm_nonneg _)) hH)
  have hu := (actual_inverse_chain_coefficients η τ ξ x a hW hU hc hD heq).1
  have hn := congrArg norm hu
  change ‖jointCoordinateDerivative explicitRightInverse (x.1, actualPhysicalCoordinate η τ ξ a x) *
    actualCoordinateMultiplier η τ ξ x a‖ = ‖(1 : ℂ)‖ at hn
  rw [norm_mul, norm_one] at hn
  apply (div_le_iff₀ hC).mpr
  calc
    1 = ‖jointCoordinateDerivative explicitRightInverse (x.1, actualPhysicalCoordinate η τ ξ a x)‖ *
        ‖actualCoordinateMultiplier η τ ξ x a‖ := hn.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmult (norm_nonneg _)

end IsingBulk.AnisoF002.Isotropic
