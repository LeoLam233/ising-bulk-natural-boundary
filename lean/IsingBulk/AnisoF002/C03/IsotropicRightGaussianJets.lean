import IsingBulk.AnisoF002.C03.IsotropicCompactGaussianJets
import IsingBulk.AnisoF002.C03.IsotropicCompactDerivativePartition

/-!
# Every constrained mean in the original physical right coefficient

The exact original-box coefficient is the finite sum of all compact
lifts. This file integrates the Gaussian bound over that complete sum.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric MeasureTheory
open scoped Topology BigOperators ContDiff

theorem rightGaussianCoefficientEnvelope_succ (κ A B : ℝ) (p N : ℕ) :
    (N : ℝ) * rightGaussianCoefficientEnvelope κ A B p N =
      rightGaussianCoefficientEnvelope κ A B (p + 1) N := by
  unfold rightGaussianCoefficientEnvelope
  rw [pow_succ]
  ring

theorem exists_actual_right_gaussian_jets (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ κ : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < κ ∧
      ∀ δB ρB : ℝ, RightCutoffGeometry b δB ρB → δB ≤ β → ρB + δB / 2 ≤ β →
      ∀ j : ℕ, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ n : ℕ, j + 1 ≤ (n + 4).choose 2 →
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 → ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1,
      ∀ a : ℝ, ∀ ε ∈ Ioo 0 δ,
        ‖iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ
          (actualLowerRightCutoff η b δB ρB (n + 4)) a) (isotropicRadialParameter α ε)‖ ≤
          rightGaussianCoefficientEnvelope κ A B (rightJetPolynomialOrder j + 1) (n + 4) *
            (1 + |Real.log ε|) := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_compact_mean_gaussian_jets α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, κ, hδ, hδβ, hκ, hbound⟩ := hdata η hη hwidth
  refine ⟨δ, κ, hδ, hδβ, hκ, ?_⟩
  intro δB ρB hcut hδB hρB j
  obtain ⟨A, B, hA, hB, hf⟩ := hbound δB ρB hcut hδB hρB j
  refine ⟨A, B, hA, hB, ?_⟩
  intro n hn σ hσ τ hτ ξ hξ a ε hε
  have hσnorm : ‖σ‖ ≤ 1 := by rcases hσ with rfl | rfl <;> simp
  have hs := (isotropicRadialParameter_estimates α ε hα hε.1
    (hε.2.le.trans (hδβ.trans hβ1))).2.2.2.1
  rw [actual_right_parameter_jets_centered_lifts hcut hδB hρB η τ ξ a σ
    (isotropicRadialParameter α ε) hη hτ.1 hξ.1 hσnorm hs j]
  apply (norm_sum_le _ _).trans
  have hsum := Finset.sum_le_sum (s := admissibleRightLifts (n + 4) b β a)
    (fun l _ => hf n hn σ hσ τ hτ ξ hξ (constrainedRightMean (n + 4) b a l - b) ε hε)
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : ((admissibleRightLifts (n + 4) b β a).card : ℝ) ≤ (n + 4 : ℕ) := by
    exact_mod_cast admissibleRightLifts_card_le (n + 4) (by omega) b β a hb.2 hβ1
  have he := rightGaussianCoefficientEnvelope_nonneg (κ := κ) hA.le hB.le (rightJetPolynomialOrder j) (n + 4)
  apply hsum.trans ((mul_le_mul_of_nonneg_right hc (mul_nonneg he (by positivity))).trans_eq ?_)
  rw [← mul_assoc, rightGaussianCoefficientEnvelope_succ]

end
end IsingBulk.AnisoF002.Isotropic
