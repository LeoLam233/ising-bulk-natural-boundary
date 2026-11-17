import IsingBulk.AnisoF002.C03.NegativeCoefficientDisks
import IsingBulk.AnisoF002.RegularTail.GaussianEnvelope
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Summable actual coefficient jets, uniformly up to the negative boundary

Cauchy's estimate is applied only to the proved c/N² coefficient disks.
The resulting full-jet majorant is summable for every fixed order and
uniform on the entire small inward interval, including its endpoint.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

namespace NegativeCoefficientControl
variable {B : ℂ → ℂ} {φ : ℝ} (d : NegativeCoefficientControl B φ)

theorem exists_coefficient_uniform_jets :
    ∃ M kappa : ℝ, 0 < M ∧ 0 < kappa ∧
      ∀ j n : ℕ, Odd (n + 1) → ∀ eps : ℝ, 0 ≤ eps → eps ≤ d.eps0 →
        ‖iteratedDeriv j (negativeCanonicalCoefficient B φ n) (-(eps : ℂ))‖ ≤
          (j.factorial * M / d.coefficientConstant ^ j) *
            ((n + 1 : ℕ) : ℝ) ^ (2 * j + 1) *
              Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨M, kappa, hM, hk, hbound⟩ := d.exists_coefficient_gaussian_disks
  refine ⟨M, kappa, hM, hk, ?_⟩
  intro j n hn eps he he0
  have hr := d.coefficientRadius_pos hn.pos
  have hcont : DiffContOnCl ℂ (negativeCanonicalCoefficient B φ n)
      (Metric.ball (-(eps : ℂ)) (d.coefficientRadius (n + 1))) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (ne_of_gt hr)]
    exact (d.coefficient_analytic_on_disk hn he he0).differentiableOn
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr
    hcont
    (fun u hu => hbound n hn eps he he0 u (Metric.sphere_subset_closedBall hu))
  have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn.pos)
  have hc0 : d.coefficientConstant ≠ 0 := ne_of_gt d.coefficientConstant_pos
  convert hC using 1
  unfold coefficientRadius
  rw [div_pow, pow_add, pow_mul, pow_one]
  field_simp

theorem exists_summable_odd_jet_majorant (j : ℕ) :
    ∃ H : ℕ → ℝ, Summable H ∧ (∀ n, 0 ≤ H n) ∧
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ d.eps0 → ∀ n : ℕ,
        ‖iteratedDeriv j (negativeCanonicalCoefficient B φ (2 * n)) (-(eps : ℂ))‖ ≤ H n := by
  obtain ⟨M, kappa, hM, hk, hbound⟩ := d.exists_coefficient_uniform_jets
  let K : ℝ := j.factorial * M / d.coefficientConstant ^ j
  let H : ℕ → ℝ := fun n => K * ((2 * n + 1 : ℕ) : ℝ) ^ (2 * j + 1) *
    Real.exp (-kappa * ((2 * n + 1 : ℕ) : ℝ) ^ 2)
  have hK : 0 ≤ K := div_nonneg (mul_nonneg (Nat.cast_nonneg _) hM.le)
    (pow_nonneg d.coefficientConstant_pos.le _)
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (2 * j + 1) * Real.exp (-kappa * (n : ℝ) ^ 2)) := by
    simpa only [zero_mul, add_zero] using gaussian_log_envelope_summable
      (2 * j + 1) hk (show (0 : ℝ) ≤ 0 by rfl)
  have hH : Summable H := by
    have hh := (hs.mul_left K).comp_injective
      (show Function.Injective (fun n : ℕ => 2 * n + 1) from fun a b hab => by
        dsimp only at hab
        omega)
    convert hh using 1
    funext n
    dsimp [H]
    ring
  refine ⟨H, hH, fun n => mul_nonneg (mul_nonneg hK (pow_nonneg (Nat.cast_nonneg _) _))
    (Real.exp_pos _).le, ?_⟩
  intro eps he he0 n
  exact hbound j (2 * n) (by exact ⟨n, rfl⟩) eps he he0

include d in
theorem odd_boundary_jets_summable (j : ℕ) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (negativeCanonicalCoefficient B φ (2 * n)) 0‖) := by
  obtain ⟨H, hH, _, hb⟩ := d.exists_summable_odd_jet_majorant j
  apply hH.of_norm_bounded
  intro n
  simpa only [Complex.ofReal_zero, neg_zero, norm_norm] using hb 0 le_rfl d.eps0_pos.le n

include d in
theorem odd_coefficient_jet_boundary_limit (j : ℕ) :
    Tendsto (fun eps : ℝ => ∑' n : ℕ,
      iteratedDeriv j (negativeCanonicalCoefficient B φ (2 * n)) (-(eps : ℂ)))
      (𝓝[≥] 0) (𝓝 (∑' n : ℕ, iteratedDeriv j (negativeCanonicalCoefficient B φ (2 * n)) 0)) := by
  obtain ⟨H, hH, _, hb⟩ := d.exists_summable_odd_jet_majorant j
  apply tendsto_tsum_of_dominated_convergence hH
  · intro n
    have ha := d.coefficient_analytic_on_disk (n := 2 * n) (by exact ⟨n, rfl⟩)
      (eps := 0) le_rfl d.eps0_pos.le (0 : ℂ)
      (show (0 : ℂ) ∈ Metric.closedBall (-(0 : ℂ)) (d.coefficientRadius (2 * n + 1)) by
        simp only [neg_zero, Metric.mem_closedBall, dist_self]
        exact (d.coefficientRadius_pos (by omega)).le)
    have hc : ContinuousAt (iteratedDeriv j (negativeCanonicalCoefficient B φ (2 * n))) 0 := by
      simpa only [iteratedDeriv_eq_iterate] using (ha.iterated_deriv j).continuousAt
    have hp : Tendsto (fun eps : ℝ => -(eps : ℂ)) (𝓝[≥] 0) (𝓝 (0 : ℂ)) := by
      simpa only [Complex.ofReal_zero, neg_zero] using
        ((Complex.continuous_ofReal.tendsto (0 : ℝ)).neg.mono_left nhdsWithin_le_nhds)
    exact hc.tendsto.comp hp
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      (Iio_mem_nhds d.eps0_pos)] with eps he he0
    exact hb eps he he0.le

end NegativeCoefficientControl
end
end IsingBulk.AnisoF002.NegativeHT
