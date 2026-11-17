import IsingBulk.AnisoF002.C03.RegularIsotropicFiniteControl

/-!
# Complete finite-particle estimates from all actual constrained means

The finite sums retain every admissible integer lift, the mixed
coefficient and all named original anchors. The common control used
here is constructed in RegularIsotropicFiniteControl.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter

theorem finite_sum_logarithmic_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hb : ∀ i ∈ s, ∃ e A : ℝ, 0 < e ∧ 0 < A ∧
      ∀ ε ∈ Ioo 0 e, ‖f i ε‖ ≤ A * (1 + |Real.log ε|)) :
    ∃ e A : ℝ, 0 < e ∧ 0 < A ∧
      ∀ ε ∈ Ioo 0 e, ‖∑ i ∈ s, f i ε‖ ≤ A * (1 + |Real.log ε|) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro ε _
    simp only [Finset.sum_empty, norm_zero, one_mul]
    positivity
  | @insert i s hi ih =>
    obtain ⟨ei, A, hei, hA, hbi⟩ := hb i (Finset.mem_insert_self _ _)
    obtain ⟨es, B, hes, hB, hbs⟩ := ih (fun k hk => hb k (Finset.mem_insert_of_mem hk))
    refine ⟨min ei es, A + B, lt_min hei hes, add_pos hA hB, ?_⟩
    intro ε hε
    rw [Finset.sum_insert hi]
    exact (norm_add_le _ _).trans ((add_le_add
      (hbi ε ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩)
      (hbs ε ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩)).trans_eq (by ring))

theorem isotropic_boundary_dispersion_gt_neg_one {α : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (μ : ℝ) :
    -1 < 2 * Real.cos α - Real.cos μ := by
  have hc := Real.cos_pos_of_mem_Ioo
    (show α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from ⟨by linarith [Real.pi_pos], hhalf⟩)
  linarith only [hc, Real.cos_le_one μ]

theorem constrainedRightMean_lift_injective {N : ℕ} (hN : 0 < N) (b phase : ℝ) :
    Function.Injective (fun k : ℤ => constrainedRightMean N b phase k - b) := by
  intro k l hkl
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [constrainedRightMean, add_sub_cancel_left] at hkl
  have hm := congrArg (fun x : ℝ => x * N) hkl
  simp only [div_mul_cancel₀ _ hNr] at hm
  have he : (k : ℝ) = l := by nlinarith only [hm, Real.pi_pos]
  exact_mod_cast he

namespace ActualFinitePartitionControl
variable {α b : ℝ} (c : ActualFinitePartitionControl α b)

def meanJet (n j : ℕ) (phase : ℝ) (σ : ℂ) (k : ℤ) (ε : ℝ) : ℂ :=
  iteratedDeriv j (compactMeanPhysicalCoefficient (n + 1) c.eta c.tau 1 b c.cutWidth c.sliver
    (constrainedRightMean (n + 2) b phase k - b) σ) (isotropicRadialParameter α ε)

def regularJetRemainder (n j : ℕ) (phase : ℝ) (σ : ℂ) (ε : ℝ) : ℂ :=
  iteratedDeriv j (mixedPhysicalCoefficient (n + 1) c.eta c.tau phase σ) (isotropicRadialParameter α ε) +
    2 * ∑ a : Fin (n + 2), iteratedDeriv j (actualWeightedParticleIntegral c.eta c.tau 1 σ
      (actualLowerAnchorCutoff c.eta b c.cutWidth c.sliver a) phase) (isotropicRadialParameter α ε)

theorem partition_jets (n j : ℕ) (phase : ℝ) (hphase : phase = 0 ∨ phase = Real.pi)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) (ε : ℝ) (hε : ε ∈ Ioo 0 c.radius) :
    iteratedDeriv j (isotropicFullParticleCoefficient (n + 1) phase σ) (isotropicRadialParameter α ε) =
      c.regularJetRemainder n j phase σ ε +
        2 * ∑ k ∈ admissibleRightLifts (n + 2) b c.buffer phase, c.meanJet n j phase σ k ε := by
  rw [c.partition n phase hphase σ hσ j ε hε]
  unfold regularJetRemainder meanJet
  ring

theorem regularJetRemainder_bound (n j : ℕ) (phase : ℝ) (σ : ℂ) (hσ : ‖σ‖ ≤ 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ ε ∈ Ioo 0 c.radius, ‖c.regularJetRemainder n j phase σ ε‖ ≤ A := by
  obtain ⟨M, hM, hm⟩ := c.mixed_bound n j
  obtain ⟨A, hA, ha⟩ := c.anchor_bound n j
  refine ⟨M + 2 * A + 1, by positivity, ?_⟩
  intro ε hε
  have hs := (originalAnchorJetNorm_bounds_complete_sum j n c.eta c.tau b c.cutWidth c.sliver phase σ
    (isotropicRadialParameter α ε)).trans (ha phase σ hσ ε hε)
  unfold regularJetRemainder
  calc
    _ ≤ _ + ‖(2 : ℂ) * _‖ := norm_add_le _ _
    _ ≤ M + 2 * A := by
      rw [norm_mul]
      norm_num only [Complex.norm_ofNat]
      exact add_le_add (hm phase σ hσ ε hε) (mul_le_mul_of_nonneg_left hs (by norm_num))
    _ ≤ _ := by linarith

theorem admissible_mean_bounds (n : ℕ) (phase : ℝ) (k : ℤ)
    (hk : k ∈ admissibleRightLifts (n + 2) b c.buffer phase) :
    constrainedRightMean (n + 2) b phase k - b ∈ Ioo (-Real.pi) Real.pi ∧
      constrainedRightMean (n + 2) b phase k - b < α := by
  obtain ⟨hl, hu⟩ := (admissibleRightLifts_mem_iff _ _ _ _ _).1 hk
  have hN : (0 : ℝ) < (n + 2 : ℕ) := by positivity
  have hlo : -b - c.buffer ≤ constrainedRightMean (n + 2) b phase k - b := by
    simp only [constrainedRightMean, add_sub_cancel_left]
    apply (le_div_iff₀ hN).2
    nlinarith only [hl]
  have hup : constrainedRightMean (n + 2) b phase k - b ≤ c.buffer := by
    simp only [constrainedRightMean, add_sub_cancel_left]
    apply (div_le_iff₀ hN).2
    nlinarith only [hu]
  refine ⟨⟨?_, ?_⟩, hup.trans_lt c.buffer_lt_alpha⟩
  · linarith only [hlo, c.buffer_lt_pi_sub]
  · linarith only [hup, c.buffer_lt_pi_sub, c.cutoff.b_pos]

theorem nonresonant_means_log_bound (n j : ℕ) (phase : ℝ) (σ : ℂ)
    (hσ : σ = 1 ∨ σ = -1) (s : Finset ℤ)
    (hx : ∀ k ∈ s, -1 < 2 * Real.cos α - Real.cos (constrainedRightMean (n + 2) b phase k - b))
    (hx1 : ∀ k ∈ s, 2 * Real.cos α - Real.cos (constrainedRightMean (n + 2) b phase k - b) ≠ 1)
    (hden : ∀ k ∈ s, 1 - σ * upperBoundaryRoot
      (2 * Real.cos α - Real.cos (constrainedRightMean (n + 2) b phase k - b)) ^ (n + 2) ≠ 0) :
    ∃ e A : ℝ, 0 < e ∧ 0 < A ∧ ∀ ε ∈ Ioo 0 e,
      ‖∑ k ∈ s, c.meanJet n j phase σ k ε‖ ≤ A * (1 + |Real.log ε|) := by
  apply finite_sum_logarithmic_bound
  intro k hk
  obtain ⟨e, A, he, _, hA, hb⟩ := c.nonresonant_bound n _ σ hσ (hx k hk) (hx1 k hk) (hden k hk) j
  exact ⟨e, A, he, hA, hb⟩

theorem full_particle_nonresonant_log_bound (n j : ℕ) (phase : ℝ)
    (hphase : phase = 0 ∨ phase = Real.pi) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (hx : ∀ k ∈ admissibleRightLifts (n + 2) b c.buffer phase,
      -1 < 2 * Real.cos α - Real.cos (constrainedRightMean (n + 2) b phase k - b))
    (hx1 : ∀ k ∈ admissibleRightLifts (n + 2) b c.buffer phase,
      2 * Real.cos α - Real.cos (constrainedRightMean (n + 2) b phase k - b) ≠ 1)
    (hden : ∀ k ∈ admissibleRightLifts (n + 2) b c.buffer phase, 1 - σ * upperBoundaryRoot
      (2 * Real.cos α - Real.cos (constrainedRightMean (n + 2) b phase k - b)) ^ (n + 2) ≠ 0) :
    ∃ e A : ℝ, 0 < e ∧ 0 < A ∧ ∀ ε ∈ Ioo 0 e,
      ‖iteratedDeriv j (isotropicFullParticleCoefficient (n + 1) phase σ)
        (isotropicRadialParameter α ε)‖ ≤ A * (1 + |Real.log ε|) := by
  have hσnorm : ‖σ‖ ≤ 1 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨A, hA, ha⟩ := c.regularJetRemainder_bound n j phase σ hσnorm
  obtain ⟨e, B, he, hB, hb⟩ := c.nonresonant_means_log_bound n j phase σ hσ _ hx hx1 hden
  refine ⟨min c.radius e, A + 2 * B, lt_min c.radius_pos he, by positivity, ?_⟩
  intro ε hε
  have hεr : ε ∈ Ioo 0 c.radius := ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hεe : ε ∈ Ioo 0 e := ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
  rw [c.partition_jets n j phase hphase σ hσ ε hεr]
  calc
    _ ≤ _ + ‖(2 : ℂ) * _‖ := norm_add_le _ _
    _ ≤ A + 2 * (B * (1 + |Real.log ε|)) := by
      rw [norm_mul]
      norm_num only [Complex.norm_ofNat]
      exact add_le_add (ha ε hεr) (mul_le_mul_of_nonneg_left (hb ε hεe) (by norm_num))
    _ ≤ _ := by nlinarith [abs_nonneg (Real.log ε)]

end ActualFinitePartitionControl

theorem exists_actual_nonresonant_full_particle_bound (n j : ℕ) (α b phase : ℝ) (σ : ℂ)
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hphase : phase = 0 ∨ phase = Real.pi) (hσ : σ = 1 ∨ σ = -1)
    (hx1 : ∀ k : ℤ, 2 * Real.cos α - Real.cos ((2 * Real.pi * k + phase) / (n + 2 : ℕ)) ≠ 1)
    (hden : ∀ k : ℤ, 1 - σ * upperBoundaryRoot
      (2 * Real.cos α - Real.cos ((2 * Real.pi * k + phase) / (n + 2 : ℕ))) ^ (n + 2) ≠ 0) :
    ∃ e A : ℝ, 0 < e ∧ 0 < A ∧ ∀ ε ∈ Ioo 0 e,
      ‖iteratedDeriv j (isotropicFullParticleCoefficient (n + 1) phase σ)
        (isotropicRadialParameter α ε)‖ ≤ A * (1 + |Real.log ε|) := by
  obtain ⟨c⟩ := exists_actual_finite_partition_control α b hα hhalf hb hpoint
  apply c.full_particle_nonresonant_log_bound n j phase hphase σ hσ
  · intro k _
    exact isotropic_boundary_dispersion_gt_neg_one hα hhalf _
  · intro k _
    simpa only [constrainedRightMean, add_sub_cancel_left] using hx1 k
  · intro k _
    simpa only [constrainedRightMean, add_sub_cancel_left] using hden k

end IsingBulk.AnisoF002.Isotropic
