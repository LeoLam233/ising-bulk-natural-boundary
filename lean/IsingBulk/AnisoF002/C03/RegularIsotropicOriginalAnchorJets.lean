import IsingBulk.AnisoF002.C03.RegularIsotropicCompactAnchorJets

/-!
# Every original anchored particle coefficient and every compact mean

The literal periodic anchor is periodized exactly into all admissible
compact means. Each named anchor is retained. At most N means and N
anchors cost only two further powers of N in the Gaussian envelope.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter MeasureTheory

theorem gaussianEnvelope_mul_particle_square (κ A B : ℝ) (p N : ℕ) :
    (N : ℝ) * ((N : ℝ) * rightGaussianCoefficientEnvelope κ A B p N) =
      rightGaussianCoefficientEnvelope κ A B (p + 2) N := by
  unfold rightGaussianCoefficientEnvelope
  rw [pow_add]
  ring

theorem exists_actual_original_anchor_gaussian_jets (α b δB : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hδB : 0 < δB) (hleft : b + δB < Real.pi) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ β → RightCutoffGeometry b δB ρ →
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b → 2 * η ≤ Real.sin (ρ / 2) →
      ∃ δ κ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < κ ∧
      ∀ j : ℕ, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ n : ℕ, ∀ σ : ℂ, ‖σ‖ ≤ 1 → ∀ τ ∈ Icc 0 δ, ∀ m : ℝ, ∀ ε ∈ Ioo 0 δ,
        (∑ a : Fin (n + 2), ‖iteratedDeriv j (actualWeightedParticleIntegral η τ 1 σ
          (actualLowerAnchorCutoff η b δB ρ a) m) (isotropicRadialParameter α ε)‖) ≤
          rightGaussianCoefficientEnvelope κ A B (anchorJetPolynomialOrder j + 2) (n + 2) := by
  obtain ⟨β₀, hβ₀, hβ₀1, hcompact⟩ := exists_actual_compact_anchor_gaussian_jets α b δB hα hb hpoint hδB hleft
  let β := min β₀ (Real.pi / 4)
  have hβ : 0 < β := lt_min hβ₀ (by positivity)
  have hb₀ : β ≤ β₀ := min_le_left _ _
  have hbπ : β ≤ Real.pi / 4 := min_le_right _ _
  refine ⟨β, hβ, hb₀.trans hβ₀1, ?_⟩
  intro ρ hρ hρβ hcut η hη hwidth hgap
  have hρπ : ρ < Real.pi / 2 := (hρβ.trans hbπ).trans_lt (by linarith only [Real.pi_pos])
  obtain ⟨δ, κ, hδ, hδ1, hκ, hbound⟩ := hcompact ρ hρ (hρβ.trans hb₀) hcut η hη hwidth hgap
  refine ⟨δ, κ, hδ, hδ1, hκ, ?_⟩
  intro j
  obtain ⟨A, B, hA, hB, hjet⟩ := hbound j
  refine ⟨A, B, hA, hB, ?_⟩
  intro n σ hσ τ hτ m ε hε
  let M := rightGaussianCoefficientEnvelope κ A B (anchorJetPolynomialOrder j) (n + 2)
  have hM : 0 ≤ M := rightGaussianCoefficientEnvelope_nonneg hA.le hB.le _ _
  have hrad := isotropicRadialParameter_estimates α ε hα hε.1 (hε.2.le.trans hδ1)
  have hcard : ((admissibleRightLifts (n + 2) Real.pi ρ m).card : ℝ) ≤ (n + 2 : ℕ) := by
    exact_mod_cast admissibleAnchorLifts_card_le (n + 2) (by omega) ρ m hρπ
  have hanchor (a : Fin (n + 2)) :
      ‖iteratedDeriv j (actualWeightedParticleIntegral η τ 1 σ
        (actualLowerAnchorCutoff η b δB ρ a) m) (isotropicRadialParameter α ε)‖ ≤ (n + 2 : ℕ) * M := by
    rw [actual_original_anchor_parameter_jets_centered_lifts hη hρ hρπ.le hgap b δB τ 1 m
      hτ.1 zero_le_one a σ _ hσ hrad.2.2.2.1 j]
    calc
      _ ≤ ∑ l ∈ admissibleRightLifts (n + 2) Real.pi ρ m,
          ‖iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ 1
            ((2 * Real.pi * l + m) / (n + 2 : ℕ)) σ (actualLowerCompactAnchorCutoff η b δB ρ a))
            (isotropicRadialParameter α ε)‖ := norm_sum_le _ _
      _ ≤ ∑ _l ∈ admissibleRightLifts (n + 2) Real.pi ρ m, M :=
        Finset.sum_le_sum (fun l _ => hjet n a σ hσ τ hτ _ ε hε)
      _ = ((admissibleRightLifts (n + 2) Real.pi ρ m).card : ℝ) * M := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hM
  calc
    _ ≤ ∑ _a : Fin (n + 2), (n + 2 : ℕ) * M := Finset.sum_le_sum (fun a _ => hanchor a)
    _ = (n + 2 : ℕ) * ((n + 2 : ℕ) * M) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = _ := gaussianEnvelope_mul_particle_square κ A B (anchorJetPolynomialOrder j) (n + 2)

end IsingBulk.AnisoF002.Isotropic
