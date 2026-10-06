import IsingBulk.First.ComplementAuxiliary

/-! Auxiliary integrability for the literal finite selected-factor type. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set
open scoped BigOperators

/-- Sum of auxiliary radii, as in the manuscript. -/
def finiteAuxiliaryRadius {ι : Type*} [Fintype ι] (ξ : ι → ℝ) : ℝ := ∑ i, ξ i

def finiteAuxiliaryTail (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {ξ | (∀ i, 0 ≤ ξ i) ∧ 1 ≤ finiteAuxiliaryRadius ξ}

/-- On the positive orthant the sum dominates the ambient product norm. -/
theorem norm_le_finiteAuxiliaryRadius {ι : Type*} [Fintype ι] {ξ : ι → ℝ}
    (hξ : ∀ i, 0 ≤ ξ i) : ‖ξ‖ ≤ finiteAuxiliaryRadius ξ := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => hξ i)).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hξ i)]
  exact Finset.single_le_sum (fun j _ => hξ j) (Finset.mem_univ i)

/-- After q=ell+j+1 integrations by parts the remaining power is integrable.
This exact majorant replaces the source's auxiliary radial-volume calculation. -/
theorem finite_auxiliary_decay_integrable (ι : Type*) [Fintype ι] :
    Integrable (fun ξ : ι → ℝ => (1 + ‖ξ‖) ^ (-((Fintype.card ι : ℝ) + 1))) := by
  apply integrable_one_add_norm
  simp

/-- The actual positive-orthant tail is controlled by that full-space majorant. -/
theorem finite_auxiliary_tail_power_bound {ι : Type*} [Fintype ι] {ξ : ι → ℝ}
    (hξ : ξ ∈ finiteAuxiliaryTail ι) :
    (finiteAuxiliaryRadius ξ)⁻¹ ^ (Fintype.card ι + 1) ≤
      (2 : ℝ) ^ (Fintype.card ι + 1) * (1 + ‖ξ‖)⁻¹ ^ (Fintype.card ι + 1) := by
  have hR : 0 < finiteAuxiliaryRadius ξ := lt_of_lt_of_le zero_lt_one hξ.2
  have hnorm := norm_le_finiteAuxiliaryRadius hξ.1
  have hd : 0 < 1 + ‖ξ‖ := by positivity
  have hi : (finiteAuxiliaryRadius ξ)⁻¹ ≤ 2 * (1 + ‖ξ‖)⁻¹ := by
    rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hR hd]
    linarith [hξ.2]
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr hR.le) hi (Fintype.card ι + 1)
  simpa only [mul_pow] using hp

/-- Natural-power and real-power forms of the same full-space majorant. -/
theorem finite_auxiliary_majorant_power_eq {ι : Type*} [Fintype ι] (ξ : ι → ℝ) :
    (1 + ‖ξ‖)⁻¹ ^ (Fintype.card ι + 1) = (1 + ‖ξ‖) ^ (-((Fintype.card ι : ℝ) + 1)) := by
  rw [show -((Fintype.card ι : ℝ) + 1) = -((Fintype.card ι + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow]

/-- The remaining auxiliary positive-orthant tail is genuinely integrable. -/
theorem finite_auxiliary_tail_integrable (ι : Type*) [Fintype ι] :
    IntegrableOn (fun ξ : ι → ℝ => (finiteAuxiliaryRadius ξ)⁻¹ ^ (Fintype.card ι + 1))
      (finiteAuxiliaryTail ι) := by
  have hT : MeasurableSet (finiteAuxiliaryTail ι) := by
    have hpos : MeasurableSet {ξ : ι → ℝ | ∀ i, 0 ≤ ξ i} := by
      have hp (i : ι) : MeasurableSet {ξ : ι → ℝ | (0 : ℝ) ≤ ξ i} :=
        measurableSet_le measurable_const (measurable_pi_apply i)
      convert MeasurableSet.iInter hp using 1
      ext ξ
      simp
    have hrad : MeasurableSet {ξ : ι → ℝ | 1 ≤ finiteAuxiliaryRadius ξ} :=
      measurableSet_le measurable_const (by unfold finiteAuxiliaryRadius; fun_prop)
    exact hpos.inter hrad
  have hg := (finite_auxiliary_decay_integrable ι).const_mul ((2 : ℝ) ^ (Fintype.card ι + 1))
  apply hg.integrableOn.mono'
  · exact (show Measurable (fun ξ : ι → ℝ => (finiteAuxiliaryRadius ξ)⁻¹ ^ (Fintype.card ι + 1)) by
      unfold finiteAuxiliaryRadius; fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hT] with ξ hξ
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr
      (le_trans zero_le_one hξ.2)) _)]
    simpa only [finite_auxiliary_majorant_power_eq] using finite_auxiliary_tail_power_bound hξ


end
end IsingBulk.First
