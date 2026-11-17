import IsingBulk.AnisoF002.C03.IsotropicFullSeriesRadialJets

/-!
# Complete physical noncancellation from the actual first coefficient

Every lower same-parity coefficient, the actual first coefficient, and
the entire higher same-parity series are retained. The complete physical
majorants make the infinite remainder negligible at the first scale.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem exists_actual_higher_parity_jet_bound (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (m K j : ℕ) (hK : 1 ≤ m + 2 * K)
    (hret : j + 1 ≤ (m + 2 * (K + 1) + 1).choose 2)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) (a : ℝ) (ha : a = 0 ∨ a = Real.pi) :
    ∃ δ B : ℝ, 0 < δ ∧ 0 ≤ B ∧ ∀ ε ∈ Ioo 0 δ,
      Summable (fun n : ℕ => ‖iteratedDeriv j
        (isotropicFullParticleCoefficient (m + 2 * (n + (K + 1))) a σ)
          (isotropicRadialParameter α ε)‖) ∧
      ‖∑' n : ℕ, iteratedDeriv j
        (isotropicFullParticleCoefficient (m + 2 * (n + (K + 1))) a σ)
          (isotropicRadialParameter α ε)‖ ≤ B * (1 + |Real.log ε|) := by
  obtain ⟨δ, hδ, _, hmajor⟩ := exists_actual_full_particle_summable_jet_majorants α b hα hb hpoint
  obtain ⟨M, hM0, hMs, hMb⟩ := hmajor j
  let P : ℕ → ℝ := fun n => M (m + 2 * (n + (K + 1)) - 3)
  have hPs : Summable P := hMs.comp_injective (fun n k he => by omega)
  refine ⟨δ, ∑' n : ℕ, P n, hδ, tsum_nonneg (fun n => hM0 _), ?_⟩
  intro ε hε
  have hb' (n : ℕ) : ‖iteratedDeriv j
      (isotropicFullParticleCoefficient (m + 2 * (n + (K + 1))) a σ)
        (isotropicRadialParameter α ε)‖ ≤ P n * (1 + |Real.log ε|) := by
    have hindex : m + 2 * (n + (K + 1)) - 3 + 3 = m + 2 * (n + (K + 1)) := by omega
    have hbudget : j + 1 ≤ (m + 2 * (n + (K + 1)) - 3 + 4).choose 2 :=
      hret.trans (Nat.choose_le_choose 2 (by omega))
    simpa only [hindex] using hMb (m + 2 * (n + (K + 1)) - 3) hbudget σ hσ a ha ε hε
  have hMs' := hPs.mul_right (1 + |Real.log ε|)
  have hs := hMs'.of_nonneg_of_le (fun n => norm_nonneg _) hb'
  refine ⟨hs, (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hb' hMs').trans_eq ?_)⟩
  exact tsum_mul_right

theorem actual_complete_series_first_scaled_limit (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (m K j l : ℕ) (hK : 1 ≤ m + 2 * K) (hl : 0 < l)
    (hret : j + 1 ≤ (m + 2 * (K + 1) + 1).choose 2)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) (a : ℝ) (ha : a = 0 ∨ a = Real.pi)
    (A : ℂ)
    (hfirst : Tendsto (fun s : ℝ => (s : ℂ) ^ l *
      iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * K) a σ)
        (isotropicRadialParameter α (s ^ 2))) (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hlower : ∀ k < K, ∃ δ B : ℝ, 0 < δ ∧ ∀ ε ∈ Ioo 0 δ,
      ‖iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * k) a σ)
        (isotropicRadialParameter α ε)‖ ≤ B * (1 + |Real.log ε|)) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ l *
      ∑' n : ℕ, iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * n) a σ)
        (isotropicRadialParameter α (s ^ 2))) (𝓝[>] (0 : ℝ)) (𝓝 A) := by
  obtain ⟨δ, B, hδ, _, hbTail⟩ := exists_actual_higher_parity_jet_bound α b hα hb hpoint
    m K j hK hret σ hσ a ha
  have htail : Tendsto (fun s : ℝ => (s : ℂ) ^ l *
      ∑' n : ℕ, iteratedDeriv j
        (isotropicFullParticleCoefficient (m + 2 * (n + (K + 1))) a σ)
          (isotropicRadialParameter α (s ^ 2))) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    radial_logarithmic_remainder_scaled_zero
      (f := fun ε => ∑' n : ℕ, iteratedDeriv j
        (isotropicFullParticleCoefficient (m + 2 * (n + (K + 1))) a σ)
          (isotropicRadialParameter α ε)) hδ hl (fun ε hε => (hbTail ε hε).2)
  have hlow : Tendsto (fun s : ℝ => ∑ k ∈ Finset.range K,
      (s : ℂ) ^ l * iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * k) a σ)
        (isotropicRadialParameter α (s ^ 2))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hterm (k : ℕ) (hk : k ∈ Finset.range K) :
        Tendsto (fun s : ℝ => (s : ℂ) ^ l *
          iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * k) a σ)
            (isotropicRadialParameter α (s ^ 2))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      obtain ⟨d, C, hd, hb⟩ := hlower k (Finset.mem_range.mp hk)
      exact radial_logarithmic_remainder_scaled_zero
        (f := fun ε => iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * k) a σ)
          (isotropicRadialParameter α ε)) (A := C) hd hl hb
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum (Finset.range K) hterm
  have hsum := (hlow.add hfirst).add htail
  simp only [zero_add, add_zero] at hsum
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s ^ 2 < δ :=
    ((show ContinuousAt (fun s : ℝ => s ^ 2) 0 by fun_prop).eventually
      (Iio_mem_nhds (by simpa using hδ))).filter_mono nhdsWithin_le_nhds
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hsδ
  have hst := (hbTail (s ^ 2) ⟨sq_pos_of_pos hs, hsδ⟩).1.of_norm
  have hfull : Summable (fun n : ℕ => iteratedDeriv j
      (isotropicFullParticleCoefficient (m + 2 * n) a σ) (isotropicRadialParameter α (s ^ 2))) :=
    (summable_nat_add_iff (K + 1)).mp hst
  have heq := hfull.sum_add_tsum_nat_add (K + 1)
  rw [Finset.sum_range_succ] at heq
  rw [← heq, mul_add, mul_add, Finset.mul_sum]

theorem actual_complete_series_no_radial_germ_of_first (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (m K j l : ℕ) (hK : 1 ≤ m + 2 * K) (hl : 0 < l)
    (hret : j + 1 ≤ (m + 2 * (K + 1) + 1).choose 2)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) (a : ℝ) (ha : a = 0 ∨ a = Real.pi)
    (A : ℂ) (hA : A ≠ 0)
    (hfirst : Tendsto (fun s : ℝ => (s : ℂ) ^ l *
      iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * K) a σ)
        (isotropicRadialParameter α (s ^ 2))) (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hlower : ∀ k < K, ∃ δ B : ℝ, 0 < δ ∧ ∀ ε ∈ Ioo 0 δ,
      ‖iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * k) a σ)
        (isotropicRadialParameter α ε)‖ ≤ B * (1 + |Real.log ε|)) :
    ¬ ∃ F : ℂ → ℂ, AnalyticAt ℂ F ((2 * Real.cos α : ℝ) : ℂ) ∧
      (∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), F (isotropicRadialParameter α ε) =
        isotropicFullParticleSeries m a σ (isotropicRadialParameter α ε)) :=
  actual_complete_series_no_radial_germ_of_scaled_jet_limit α b hα hb hpoint m σ hσ a ha j l hl A hA
    (actual_complete_series_first_scaled_limit α b hα hb hpoint m K j l hK hl hret σ hσ a ha A hfirst hlower)

end
end IsingBulk.AnisoF002.Isotropic
