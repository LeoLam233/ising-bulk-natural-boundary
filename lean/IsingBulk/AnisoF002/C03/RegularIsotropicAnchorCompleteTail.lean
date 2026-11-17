import IsingBulk.AnisoF002.C03.RegularIsotropicOriginalAnchorJets

/-!
# The complete differentiated original anchored particle tail

Every N >= 2, every named anchor, every original constrained mean and
both physical signs are included. No small population is removed.
One radial/deformation neighborhood works for all fixed derivative
orders, with a summable Gaussian envelope and uniformly small tails.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter

def originalAnchorJetNorm (j n : ℕ) (η τ b δB ρ m : ℝ) (σ S : ℂ) : ℝ :=
  ∑ a : Fin (n + 2), ‖iteratedDeriv j (actualWeightedParticleIntegral η τ 1 σ
    (actualLowerAnchorCutoff η b δB ρ a) m) S‖

theorem originalAnchorJetNorm_nonneg (j n : ℕ) (η τ b δB ρ m : ℝ) (σ S : ℂ) :
    0 ≤ originalAnchorJetNorm j n η τ b δB ρ m σ S :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem originalAnchorJetNorm_single_bound (j n : ℕ) (η τ b δB ρ m : ℝ) (σ S : ℂ)
    (a : Fin (n + 2)) :
    ‖iteratedDeriv j (actualWeightedParticleIntegral η τ 1 σ (actualLowerAnchorCutoff η b δB ρ a) m) S‖ ≤
      originalAnchorJetNorm j n η τ b δB ρ m σ S := by
  unfold originalAnchorJetNorm
  exact Finset.single_le_sum
    (f := fun i : Fin (n + 2) => ‖iteratedDeriv j (actualWeightedParticleIntegral η τ 1 σ
      (actualLowerAnchorCutoff η b δB ρ i) m) S‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ a)

theorem originalAnchorJetNorm_bounds_complete_sum (j n : ℕ) (η τ b δB ρ m : ℝ) (σ S : ℂ) :
    ‖∑ a : Fin (n + 2), iteratedDeriv j (actualWeightedParticleIntegral η τ 1 σ
      (actualLowerAnchorCutoff η b δB ρ a) m) S‖ ≤
      originalAnchorJetNorm j n η τ b δB ρ m σ S := norm_sum_le _ _

theorem exists_actual_anchor_summable_jet_majorants (α b δB : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hδB : 0 < δB) (hleft : b + δB < Real.pi) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ β → RightCutoffGeometry b δB ρ →
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b → 2 * η ≤ Real.sin (ρ / 2) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ j : ℕ, ∃ M : ℕ → ℝ, (∀ n, 0 ≤ M n) ∧ Summable M ∧
      ∀ n : ℕ, ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ τ ∈ Icc 0 δ, ∀ m : ℝ, ∀ ε ∈ Ioo 0 δ,
        originalAnchorJetNorm j n η τ b δB ρ m σ (isotropicRadialParameter α ε) ≤ M n := by
  obtain ⟨β, hβ, hβ1, hall⟩ := exists_actual_original_anchor_gaussian_jets α b δB hα hb hpoint hδB hleft
  refine ⟨β, hβ, hβ1, ?_⟩
  intro ρ hρ hρβ hcut η hη hwidth hgap
  obtain ⟨δ, κ, hδ, hδ1, hκ, hbound⟩ := hall ρ hρ hρβ hcut η hη hwidth hgap
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro j
  obtain ⟨A, B, hA, hB, hj⟩ := hbound j
  refine ⟨fun n => rightGaussianCoefficientEnvelope κ A B (anchorJetPolynomialOrder j + 2) (n + 2),
    fun n => rightGaussianCoefficientEnvelope_nonneg hA.le hB.le _ _, ?_, hj⟩
  exact (rightGaussianCoefficientEnvelope_summable hκ hA.le hB _).comp_injective
    (fun n m h => Nat.add_right_cancel h)

theorem exists_actual_anchor_complete_differentiated_tail (α b δB : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hδB : 0 < δB) (hleft : b + δB < Real.pi) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ β → RightCutoffGeometry b δB ρ →
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b → 2 * η ≤ Real.sin (ρ / 2) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ τ ∈ Icc 0 δ, ∀ m : ℝ, ∀ ε ∈ Ioo 0 δ,
        Summable (fun n => originalAnchorJetNorm j n η τ b δB ρ m σ (isotropicRadialParameter α ε)) ∧
        (∑' n, originalAnchorJetNorm j n η τ b δB ρ m σ (isotropicRadialParameter α ε)) ≤ M := by
  obtain ⟨β, hβ, hβ1, hall⟩ := exists_actual_anchor_summable_jet_majorants α b δB hα hb hpoint hδB hleft
  refine ⟨β, hβ, hβ1, ?_⟩
  intro ρ hρ hρβ hcut η hη hwidth hgap
  obtain ⟨δ, hδ, hδ1, hbound⟩ := hall ρ hρ hρβ hcut η hη hwidth hgap
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro j
  obtain ⟨M, hM0, hMs, hMb⟩ := hbound j
  refine ⟨∑' n, M n, tsum_nonneg hM0, ?_⟩
  intro σ hσ τ hτ m ε hε
  have hb' (n : ℕ) := hMb n σ hσ τ hτ m ε hε
  have hs := hMs.of_nonneg_of_le (fun n => originalAnchorJetNorm_nonneg j n η τ b δB ρ m σ _) hb'
  exact ⟨hs, hs.tsum_le_tsum hb' hMs⟩

theorem exists_actual_anchor_uniform_tail_small (α b δB : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hδB : 0 < δB) (hleft : b + δB < Real.pi) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ β → RightCutoffGeometry b δB ρ →
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b → 2 * η ≤ Real.sin (ρ / 2) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ j : ℕ, ∀ e : ℝ, 0 < e → ∃ K : ℕ,
      ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ τ ∈ Icc 0 δ, ∀ m : ℝ, ∀ ε ∈ Ioo 0 δ,
        (∑' n, originalAnchorJetNorm j (n + K) η τ b δB ρ m σ (isotropicRadialParameter α ε)) < e := by
  obtain ⟨β, hβ, hβ1, hall⟩ := exists_actual_anchor_summable_jet_majorants α b δB hα hb hpoint hδB hleft
  refine ⟨β, hβ, hβ1, ?_⟩
  intro ρ hρ hρβ hcut η hη hwidth hgap
  obtain ⟨δ, hδ, hδ1, hbound⟩ := hall ρ hρ hρβ hcut η hη hwidth hgap
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro j e he
  obtain ⟨M, _, hMs, hMb⟩ := hbound j
  have ht := (tendsto_sum_nat_add M).eventually (Iio_mem_nhds he)
  obtain ⟨K, hK⟩ := ht.exists
  refine ⟨K, ?_⟩
  intro σ hσ τ hτ m ε hε
  have hshift : Summable (fun n : ℕ => M (n + K)) :=
    hMs.comp_injective (fun n m h => Nat.add_right_cancel h)
  have hb' (n : ℕ) := hMb (n + K) σ hσ τ hτ m ε hε
  have hs := hshift.of_nonneg_of_le
    (fun n => originalAnchorJetNorm_nonneg j (n + K) η τ b δB ρ m σ _) hb'
  exact (hs.tsum_le_tsum hb' hshift).trans_lt hK

end IsingBulk.AnisoF002.Isotropic
