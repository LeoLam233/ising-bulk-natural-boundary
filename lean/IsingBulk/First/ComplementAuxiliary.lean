import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! Exact half-line reciprocals and the integrable auxiliary-variable majorant
for FIRST's fixed-order complement estimate. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set
open scoped BigOperators

/-- Product and pair denominators have this damped half-line representation. -/
theorem inverse_eq_halfLine_exponential {A : ℂ} (hA : 0 < A.re) :
    A⁻¹ = ∫ ξ : ℝ in Ioi 0, Complex.exp (-A * ξ) := by
  rw [integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hA) 0]
  simp

/-- The correct scalar multiplier for the source dispersion convention.
For Im D>0 the integral is i/D, hence the multiplier is -i. -/
theorem dispersion_inverse_eq_halfLine_exponential {D : ℂ} (hD : 0 < D.im) :
    D⁻¹ = -Complex.I * ∫ ξ : ℝ in Ioi 0, Complex.exp ((Complex.I * D) * ξ) := by
  have hreal : (Complex.I * D).re < 0 := by simpa using neg_neg_of_pos hD
  rw [integral_exp_mul_complex_Ioi hreal 0]
  have hD0 : D ≠ 0 := by intro h; simp [h] at hD
  field_simp
  simp

/-- Fixed positive damping makes each scalar half-line integral absolutely integrable. -/
theorem halfLine_exponential_integrable {A : ℂ} (hA : 0 < A.re) :
    IntegrableOn (fun ξ : ℝ => Complex.exp (-A * ξ)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hA) 0

/-- Sum of auxiliary radii, as in the manuscript. -/
def auxiliaryRadius {ell : ℕ} (ξ : Fin ell → ℝ) : ℝ := ∑ i, ξ i

def auxiliaryTail (ell : ℕ) : Set (Fin ell → ℝ) :=
  {ξ | (∀ i, 0 ≤ ξ i) ∧ 1 ≤ auxiliaryRadius ξ}

/-- On the positive orthant the sum dominates the ambient product norm. -/
theorem norm_le_auxiliaryRadius {ell : ℕ} {ξ : Fin ell → ℝ}
    (hξ : ∀ i, 0 ≤ ξ i) : ‖ξ‖ ≤ auxiliaryRadius ξ := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => hξ i)).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hξ i)]
  exact Finset.single_le_sum (fun j _ => hξ j) (Finset.mem_univ i)

/-- After q=ell+j+1 integrations by parts the remaining power is integrable.
This exact majorant replaces the source's auxiliary radial-volume calculation. -/
theorem auxiliary_decay_integrable (ell : ℕ) :
    Integrable (fun ξ : Fin ell → ℝ => (1 + ‖ξ‖) ^ (-((ell : ℝ) + 1))) := by
  apply integrable_one_add_norm
  simp

/-- The actual positive-orthant tail is controlled by that full-space majorant. -/
theorem auxiliary_tail_power_bound {ell : ℕ} {ξ : Fin ell → ℝ}
    (hξ : ξ ∈ auxiliaryTail ell) :
    (auxiliaryRadius ξ)⁻¹ ^ (ell + 1) ≤
      (2 : ℝ) ^ (ell + 1) * (1 + ‖ξ‖)⁻¹ ^ (ell + 1) := by
  have hR : 0 < auxiliaryRadius ξ := lt_of_lt_of_le zero_lt_one hξ.2
  have hnorm := norm_le_auxiliaryRadius hξ.1
  have hd : 0 < 1 + ‖ξ‖ := by positivity
  have hi : (auxiliaryRadius ξ)⁻¹ ≤ 2 * (1 + ‖ξ‖)⁻¹ := by
    rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hR hd]
    linarith [hξ.2]
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr hR.le) hi (ell + 1)
  simpa only [mul_pow] using hp

/-- Natural-power and real-power forms of the same full-space majorant. -/
theorem auxiliary_majorant_power_eq {ell : ℕ} (ξ : Fin ell → ℝ) :
    (1 + ‖ξ‖)⁻¹ ^ (ell + 1) = (1 + ‖ξ‖) ^ (-((ell : ℝ) + 1)) := by
  rw [show -((ell : ℝ) + 1) = -((ell + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow]

/-- The remaining auxiliary positive-orthant tail is genuinely integrable. -/
theorem auxiliary_tail_integrable (ell : ℕ) :
    IntegrableOn (fun ξ : Fin ell → ℝ => (auxiliaryRadius ξ)⁻¹ ^ (ell + 1))
      (auxiliaryTail ell) := by
  have hT : MeasurableSet (auxiliaryTail ell) := by
    have hpos : MeasurableSet {ξ : Fin ell → ℝ | ∀ i, 0 ≤ ξ i} := by
      have hp (i : Fin ell) : MeasurableSet {ξ : Fin ell → ℝ | (0 : ℝ) ≤ ξ i} :=
        measurableSet_le measurable_const (measurable_pi_apply i)
      convert MeasurableSet.iInter hp using 1
      ext ξ
      simp
    have hrad : MeasurableSet {ξ : Fin ell → ℝ | 1 ≤ auxiliaryRadius ξ} :=
      measurableSet_le measurable_const (by unfold auxiliaryRadius; fun_prop)
    exact hpos.inter hrad
  have hg := (auxiliary_decay_integrable ell).const_mul ((2 : ℝ) ^ (ell + 1))
  apply hg.integrableOn.mono'
  · exact (show Measurable (fun ξ : Fin ell → ℝ => (auxiliaryRadius ξ)⁻¹ ^ (ell + 1)) by
      unfold auxiliaryRadius; fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hT] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr
      (le_trans zero_le_one hξ.2)) _)]
    simpa only [auxiliary_majorant_power_eq] using auxiliary_tail_power_bound hξ

end
end IsingBulk.First
