import IsingBulk.AnisoF002.C03.IsotropicRadialSeriesJets
import IsingBulk.AnisoF002.C03.RegularIsotropicFullTail
import IsingBulk.AnisoF002.C03.IsotropicPhysicalSeries

/-!
# Local summable bounds for every actual complete parity-series jet

The finite prefix is controlled by its genuine interior holomorphy.
Every later particle is controlled by the complete original mixed,
right and anchored bounds. Thus no particle is discarded when passing
from boundary logarithmic estimates to local termwise differentiation.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators

theorem local_summable_majorant_of_tail {f : ℕ → ℝ → ℂ} {W : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U)
    (hf : ∀ n : ℕ, ContinuousAt (f n) x) (hW : ContinuousAt W x)
    (K : ℕ) {M : ℕ → ℝ} (hM0 : ∀ n, 0 ≤ M n) (hM : Summable M)
    (htail : ∀ n : ℕ, ∀ t ∈ U, ‖f (n + K) t‖ ≤ M n * W t) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧ ∃ B : ℕ → ℝ, Summable B ∧
      ∀ n : ℕ, ∀ t ∈ ball x r, ‖f n t‖ ≤ B n := by
  have hWb : ∀ᶠ t in 𝓝 x, W t < |W x| + 1 :=
    hW.eventually (Iio_mem_nhds (by linarith [le_abs_self (W x)]))
  have hpre : ∀ᶠ t in 𝓝 x, ∀ i : Fin K, ‖f i t‖ < ‖f i x‖ + 1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hf i).norm.eventually (Iio_mem_nhds (by linarith))
  have hev : ∀ᶠ t in 𝓝 x, t ∈ U ∧ W t < |W x| + 1 ∧
      ∀ i : Fin K, ‖f i t‖ < ‖f i x‖ + 1 := by
    filter_upwards [hU.mem_nhds hx, hWb, hpre] with t ht hw hp
    exact ⟨ht, hw, hp⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let B : ℕ → ℝ := fun n => if n < K then ‖f n x‖ + 1 else M (n - K) * (|W x| + 1)
  have hBs : Summable B := by
    apply (summable_nat_add_iff K).mp
    simpa only [B, show ∀ n : ℕ, ¬n + K < K from fun n => by omega,
      ite_false, Nat.add_sub_cancel_right] using hM.mul_right (|W x| + 1)
  refine ⟨r, hr, fun t ht => (hball ht).1, B, hBs, ?_⟩
  intro n t ht
  by_cases hn : n < K
  · simp only [B, ite_eq_left hn]
    exact ((hball ht).2.2 ⟨n, hn⟩).le
  · simp only [B, ite_eq_right hn]
    have he : n - K + K = n := Nat.sub_add_cancel (le_of_not_gt hn)
    have hh := htail (n - K) t (hball ht).1
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hball ht).2.1.le (hM0 _))

theorem exists_actual_complete_series_local_jet_majorants (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ m j : ℕ, ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
      ∀ a : ℝ, a = 0 ∨ a = Real.pi → ∀ x ∈ Ioo 0 δ,
      ∃ r : ℝ, 0 < r ∧ ball x r ⊆ Ioo 0 δ ∧ ∃ M : ℕ → ℝ, Summable M ∧
        ∀ n : ℕ, ∀ ε ∈ ball x r,
          ‖iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * n) a σ)
            (isotropicRadialParameter α ε)‖ ≤ M n := by
  obtain ⟨δ, hδ, hδ1, hfull⟩ := exists_actual_full_particle_summable_jet_majorants α b hα hb hpoint
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro m j σ hσ a ha x hx
  have hσnorm : ‖σ‖ ≤ 1 := by rcases hσ with rfl | rfl <;> simp
  have him := (isotropicRadialParameter_estimates α x hα hx.1 (hx.2.le.trans hδ1)).2.2.2.1
  have hf (n : ℕ) : ContinuousAt (fun ε : ℝ =>
      iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * n) a σ)
        (isotropicRadialParameter α ε)) x := by
    have hcoef := (isotropicFullParticleCoefficient_analyticAt (m + 2 * n) a σ _ hσnorm him).iterated_deriv j
    have hc : ContinuousAt (iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * n) a σ))
        (isotropicRadialParameter α x) := by
      simpa only [iteratedDeriv_eq_iterate] using hcoef.continuousAt
    exact hc.comp (isotropicRadialParameter_hasDerivAt α x hx.1).continuousAt
  have hW : ContinuousAt (fun ε : ℝ => 1 + |Real.log ε|) x :=
    continuousAt_const.add ((Real.continuousAt_log hx.1.ne').abs)
  obtain ⟨M, hM0, hMs, hMb⟩ := hfull j
  let K := j + 3
  let B : ℕ → ℝ := fun n => M (m + 2 * (n + K) - 3)
  have hBs : Summable B := hMs.comp_injective (fun n k he => by dsimp [K] at he; omega)
  apply local_summable_majorant_of_tail isOpen_Ioo hx hf hW K (fun n => hM0 _) hBs
  intro n ε hε
  have hindex : m + 2 * (n + K) - 3 + 3 = m + 2 * (n + K) := by dsimp [K]; omega
  have hret : j + 1 ≤ (m + 2 * (n + K) - 3 + 4).choose 2 :=
    (right_retention_threshold_exists j).trans (Nat.choose_le_choose 2 (by dsimp [K]; omega))
  have hh := hMb (m + 2 * (n + K) - 3) hret σ hσ a ha ε hε
  simpa only [hindex] using hh

end
end IsingBulk.AnisoF002.Isotropic
