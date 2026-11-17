import IsingBulk.AnisoF002.C03.NegativeUniformPhase
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Quantitative scalar zero construction on a closed complex disk

This is the contraction step used for the normalized full phase sum.
The radius and derivative slack are explicit; no inverse-function radius
depending on the number of angles is hidden in this statement.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology

theorem exists_unique_zero_of_deriv_close {F : ℂ → ℂ} {τ a : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hR : 0 ≤ R)
    (hd : ∀ t ∈ Metric.closedBall τ R, DifferentiableAt ℂ F t)
    (hclose : ∀ t ∈ Metric.closedBall τ R, ‖deriv F t - a‖ ≤ ‖a‖ / 2)
    (hresidual : ‖F τ‖ / ‖a‖ ≤ R / 2) :
    ∃ t ∈ Metric.closedBall τ R, F t = 0 ∧
      ‖t - τ‖ ≤ 2 * ‖F τ‖ / ‖a‖ ∧ deriv F t ≠ 0 ∧
      ∀ u ∈ Metric.closedBall τ R, F u = 0 → u = t := by
  let H : ℂ → ℂ := fun t => t - F t / a
  have haNorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hHderiv (t : ℂ) (ht : t ∈ Metric.closedBall τ R) :
      HasDerivAt H (1 - deriv F t / a) t :=
    (hasDerivAt_id t).sub ((hd t ht).hasDerivAt.div_const a)
  have hHbound (t : ℂ) (ht : t ∈ Metric.closedBall τ R) :
      ‖1 - deriv F t / a‖ ≤ (1 / 2 : ℝ) := by
    have he : 1 - deriv F t / a = (a - deriv F t) / a := by field_simp
    rw [he, norm_div, norm_sub_rev]
    apply (div_le_iff₀ haNorm).mpr
    nlinarith [hclose t ht]
  have hLip : LipschitzOnWith (1 / 2 : NNReal) H (Metric.closedBall τ R) := by
    apply (convex_closedBall τ R).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (hHderiv t ht).hasDerivWithinAt)
    intro t ht
    exact_mod_cast hHbound t ht
  have hτ : τ ∈ Metric.closedBall τ R := Metric.mem_closedBall_self hR
  have hdist (t u : ℂ) (ht : t ∈ Metric.closedBall τ R)
      (hu : u ∈ Metric.closedBall τ R) :
      ‖H t - H u‖ ≤ (1 / 2 : ℝ) * ‖t - u‖ := by
    simpa only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat] using hLip.dist_le_mul t ht u hu
  have hcenter : ‖H τ - τ‖ = ‖F τ‖ / ‖a‖ := by
    simp only [H, sub_sub_cancel_left, norm_neg, norm_div]
  have hmaps : MapsTo H (Metric.closedBall τ R) (Metric.closedBall τ R) := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm]
    have htnorm : ‖t - τ‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using ht
    calc
      ‖H t - τ‖ ≤ ‖H t - H τ‖ + ‖H τ - τ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (1 / 2 : ℝ) * ‖t - τ‖ + ‖F τ‖ / ‖a‖ :=
        add_le_add (hdist t τ ht hτ) hcenter.le
      _ ≤ R := by nlinarith
  have hcontract : ContractingWith (1 / 2 : NNReal)
      (hmaps.restrict H (Metric.closedBall τ R) (Metric.closedBall τ R)) :=
    ⟨by norm_num, hLip.mapsToRestrict hmaps⟩
  obtain ⟨t, ht, hfix, _, _⟩ := hcontract.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hmaps hτ (edist_ne_top _ _)
  have hzero : F t = 0 := by
    have hq : F t / a = 0 := by
      have hh : t - F t / a = t := hfix
      linear_combination -hh
    exact (div_eq_zero_iff.mp hq).resolve_right ha
  refine ⟨t, ht, hzero, ?_, ?_, ?_⟩
  · have hn : ‖t - τ‖ ≤ (1 / 2 : ℝ) * ‖t - τ‖ + ‖F τ‖ / ‖a‖ := by
      calc
        ‖t - τ‖ = ‖H t - τ‖ := by rw [hfix.eq]
        _ ≤ ‖H t - H τ‖ + ‖H τ - τ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (1 / 2 : ℝ) * ‖t - τ‖ + ‖F τ‖ / ‖a‖ :=
          add_le_add (hdist t τ ht hτ) hcenter.le
    simpa only [mul_div_assoc] using (show ‖t - τ‖ ≤ 2 * (‖F τ‖ / ‖a‖) by linarith)
  · intro hz
    have hh := hclose t ht
    simp only [hz, zero_sub, norm_neg] at hh
    linarith
  · intro u hu hFu
    have hHu : H u = u := by simp only [H, hFu, zero_div, sub_zero]
    have hh := hdist u t hu ht
    rw [hHu, hfix.eq] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (u - t)]))

end
end IsingBulk.AnisoF002.NegativeHT
