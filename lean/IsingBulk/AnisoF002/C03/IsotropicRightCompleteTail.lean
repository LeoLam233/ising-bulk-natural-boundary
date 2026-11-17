import IsingBulk.AnisoF002.C03.IsotropicRightGaussianSummability

/-!
# The complete differentiated actual right-sector tail

Every particle beyond an arbitrary eligible threshold is included, with
all constrained means and either physical sign. The finitely many smaller
particles are not asserted regular here: their actual coincidence and
first-chart analysis is a separate obligation.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem exists_actual_right_summable_jet_majorants (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ δB ρB : ℝ, RightCutoffGeometry b δB ρB → δB ≤ β → ρB + δB / 2 ≤ β →
      ∀ j : ℕ, ∃ M : ℕ → ℝ, (∀ n, 0 ≤ M n) ∧ Summable M ∧
      ∀ n : ℕ, j + 1 ≤ (n + 4).choose 2 →
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 → ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1,
      ∀ a : ℝ, ∀ ε ∈ Ioo 0 δ,
        ‖iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ
          (actualLowerRightCutoff η b δB ρB (n + 4)) a) (isotropicRadialParameter α ε)‖ ≤
          M n * (1 + |Real.log ε|) := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_right_gaussian_jets α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, κ, hδ, hδβ, hκ, hbound⟩ := hdata η hη hwidth
  refine ⟨δ, hδ, hδβ, ?_⟩
  intro δB ρB hcut hδB hρB j
  obtain ⟨A, B, hA, hB, hf⟩ := hbound δB ρB hcut hδB hρB j
  refine ⟨fun n => rightGaussianCoefficientEnvelope κ A B (rightJetPolynomialOrder j + 1) (n + 4),
    fun n => rightGaussianCoefficientEnvelope_nonneg hA.le hB.le _ _, ?_, hf⟩
  exact (rightGaussianCoefficientEnvelope_summable hκ hA.le hB _).comp_injective
    (fun n m h => Nat.add_right_cancel h)

theorem exists_actual_right_complete_differentiated_tail (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ δB ρB : ℝ, RightCutoffGeometry b δB ρB → δB ≤ β → ρB + δB / 2 ≤ β →
      ∀ j K : ℕ, j + 1 ≤ (K + 4).choose 2 → ∃ M : ℝ, 0 ≤ M ∧
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 → ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1,
      ∀ a : ℝ, ∀ ε ∈ Ioo 0 δ,
        Summable (fun n : ℕ => ‖iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ
          (actualLowerRightCutoff η b δB ρB (n + K + 4)) a) (isotropicRadialParameter α ε)‖) ∧
        (∑' n : ℕ, ‖iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ
          (actualLowerRightCutoff η b δB ρB (n + K + 4)) a) (isotropicRadialParameter α ε)‖) ≤
          M * (1 + |Real.log ε|) := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_right_summable_jet_majorants α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, hδ, hδβ, hbound⟩ := hdata η hη hwidth
  refine ⟨δ, hδ, hδβ, ?_⟩
  intro δB ρB hcut hδB hρB j K hK
  obtain ⟨M, hM0, hMs, hMb⟩ := hbound δB ρB hcut hδB hρB j
  have hshift : Summable (fun n : ℕ => M (n + K)) :=
    hMs.comp_injective (fun n m h => Nat.add_right_cancel h)
  refine ⟨∑' n : ℕ, M (n + K), tsum_nonneg (fun n => hM0 _), ?_⟩
  intro σ hσ τ hτ ξ hξ a ε hε
  have hmajor (n : ℕ) := hMb (n + K)
    (hK.trans (Nat.choose_le_choose 2 (by omega))) σ hσ τ hτ ξ hξ a ε hε
  have hMs' := hshift.mul_right (1 + |Real.log ε|)
  have hs := hMs'.of_nonneg_of_le (fun n => norm_nonneg _) hmajor
  refine ⟨hs, (hs.tsum_le_tsum hmajor hMs').trans_eq ?_⟩
  exact tsum_mul_right

theorem right_retention_threshold_exists (j : ℕ) : j + 1 ≤ (j + 4).choose 2 := by
  rw [Nat.choose_two_right, show j + 4 - 1 = j + 3 by omega]
  apply (Nat.le_div_iff_mul_le (by omega)).2
  nlinarith

theorem exists_actual_right_uniform_logarithmic_tail_small (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ δB ρB : ℝ, RightCutoffGeometry b δB ρB → δB ≤ β → ρB + δB / 2 ≤ β →
      ∀ j : ℕ, ∀ e : ℝ, 0 < e → ∃ K : ℕ, j + 1 ≤ (K + 4).choose 2 ∧
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 → ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1,
      ∀ a : ℝ, ∀ ε ∈ Ioo 0 δ,
        (∑' n : ℕ, ‖iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ
          (actualLowerRightCutoff η b δB ρB (n + K + 4)) a) (isotropicRadialParameter α ε)‖) <
          e * (1 + |Real.log ε|) := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_right_summable_jet_majorants α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, hδ, hδβ, hbound⟩ := hdata η hη hwidth
  refine ⟨δ, hδ, hδβ, ?_⟩
  intro δB ρB hcut hδB hρB j e he
  obtain ⟨M, _, hMs, hMb⟩ := hbound δB ρB hcut hδB hρB j
  have ht := (tendsto_sum_nat_add M).eventually (Iio_mem_nhds he)
  obtain ⟨K, hsmall, hKj⟩ := (ht.and (eventually_ge_atTop j)).exists
  have hK := (right_retention_threshold_exists j).trans (Nat.choose_le_choose 2 (by omega : j + 4 ≤ K + 4))
  refine ⟨K, hK, ?_⟩
  intro σ hσ τ hτ ξ hξ a ε hε
  have hshift : Summable (fun n : ℕ => M (n + K)) :=
    hMs.comp_injective (fun n m h => Nat.add_right_cancel h)
  have hmajor (n : ℕ) := hMb (n + K)
    (hK.trans (Nat.choose_le_choose 2 (by omega))) σ hσ τ hτ ξ hξ a ε hε
  have hMs' := hshift.mul_right (1 + |Real.log ε|)
  have hs := hMs'.of_nonneg_of_le (fun n => norm_nonneg _) hmajor
  calc
    _ ≤ ∑' n : ℕ, M (n + K) * (1 + |Real.log ε|) := hs.tsum_le_tsum hmajor hMs'
    _ = (∑' n : ℕ, M (n + K)) * (1 + |Real.log ε|) := tsum_mul_right
    _ < _ := mul_lt_mul_of_pos_right hsmall (by positivity)

end
end IsingBulk.AnisoF002.Isotropic
