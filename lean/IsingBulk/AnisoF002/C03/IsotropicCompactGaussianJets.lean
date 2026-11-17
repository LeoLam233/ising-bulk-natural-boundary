import IsingBulk.AnisoF002.C03.IsotropicCurrentCoareaBound
import IsingBulk.AnisoF002.C03.IsotropicCompactCurrentJets

/-!
# Complete physical compact-mean jets with a Gaussian particle envelope

Exactly j+1 actual numerator pairs are retained. The current identifies
complex coefficient derivatives, and the full coarea weight is integrated.
The neighborhood and Gaussian exponent are fixed before the derivative
order, particle count, mean, and physical sign.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric MeasureTheory
open scoped Topology BigOperators ContDiff

def rightJetPolynomialOrder (j : ℕ) : ℕ := (7 + 3 * j) * j + 3 + 2 * (j + 1)

def rightGaussianCoefficientEnvelope (κ A B : ℝ) (p N : ℕ) : ℝ :=
  A * (N : ℝ) ^ p * B ^ N * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) /
    ((N.factorial : ℝ) * (2 * Real.pi) ^ (N - 1))

theorem rightGaussianCoefficientEnvelope_nonneg {κ A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p N : ℕ) : 0 ≤ rightGaussianCoefficientEnvelope κ A B p N := by
  unfold rightGaussianCoefficientEnvelope
  positivity

theorem rightCurrentCoareaEnvelope_cutoff (κ C M K Cj Ag Cg : ℝ) (j N : ℕ) :
    rightCurrentCoareaEnvelope κ C M K Cj (Ag * Cg ^ N * (N : ℝ) ^ (2 * (j + 1))) j N (j + 1) =
      rightGaussianCoefficientEnvelope κ
        (8 * Cj * Ag * M ^ (j + 1) * (max 1 (Real.sqrt (Real.pi + 2))) ^ (2 * (j + 1)))
        (2 * C * K * Cg) (rightJetPolynomialOrder j) N := by
  unfold rightCurrentCoareaEnvelope rightGaussianCoefficientEnvelope rightJetPolynomialOrder
  simp only [pow_add, mul_pow]
  ring

theorem exists_actual_compact_mean_gaussian_jets (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ κ : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < κ ∧
      ∀ δB ρB : ℝ, RightCutoffGeometry b δB ρB → δB ≤ β → ρB + δB / 2 ≤ β →
      ∀ j : ℕ, ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ n : ℕ, j + 1 ≤ (n + 4).choose 2 →
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 → ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1,
      ∀ μ : ℝ, ∀ ε ∈ Ioo 0 δ,
        ‖iteratedDeriv j (compactMeanPhysicalCoefficient (n + 3) η τ ξ b δB ρB μ σ)
          (isotropicRadialParameter α ε)‖ ≤
          rightGaussianCoefficientEnvelope κ A B (rightJetPolynomialOrder j) (n + 4) *
            (1 + |Real.log ε|) := by
  obtain ⟨βJ, hβJ, hβJ1, hjets⟩ := exists_actual_compact_mean_current_jets α b hα hb hpoint
  obtain ⟨βC, hβC, _, hcoarea⟩ := exists_actual_current_integral_coarea_bound α b hα hb hpoint
  let β := min βJ βC
  have hβ : 0 < β := lt_min hβJ hβC
  have hbJ : β ≤ βJ := min_le_left _ _
  have hbC : β ≤ βC := min_le_right _ _
  refine ⟨β, hβ, hbJ.trans hβJ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δJ, hδJ, _, hj⟩ := hjets η hη hwidth
  obtain ⟨δC, κ, C, M, K, hδC, _, hκ, hC, hM, hK, hc⟩ := hcoarea η hη hwidth
  let δ := min β (min δJ δC)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdβ : δ ≤ β := min_le_left _ _
  have hdJ : δ ≤ δJ := (min_le_right _ _).trans (min_le_left _ _)
  have hdC : δ ≤ δC := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, κ, hδ, hdβ, hκ, ?_⟩
  intro δB ρB hcut hδB hρB j
  obtain ⟨Cj, hCj, hbound⟩ := hc j
  obtain ⟨Ag, Cg, hAg, hCg, hgjet⟩ := actualLowerCompactRightCutoff_jets hcut η (j + 1)
  let A := 8 * Cj * Ag * M ^ (j + 1) *
    (max 1 (Real.sqrt (Real.pi + 2))) ^ (2 * (j + 1))
  let B := 2 * C * K * Cg
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A, B, hA, hB, ?_⟩
  intro n hn σ hσ τ hτ ξ hξ μ ε hε
  obtain ⟨R, hR, hcard⟩ := Finset.exists_subset_card_eq
    (show j + 1 ≤ (indexPairs (n + 4)).card by simpa only [card_indexPairs] using hn)
  have hσnorm : ‖σ‖ ≤ 1 := by rcases hσ with rfl | rfl <;> simp
  rw [hj δB ρB hcut (hδB.trans hbJ) (hρB.trans hbJ) (n + 2) R hR j
    (by omega) σ hσnorm τ ⟨hτ.1, hτ.2.trans hdJ⟩ ξ hξ μ ε ⟨hε.1, hε.2.trans_le hdJ⟩]
  let g := actualLowerCompactRightCutoff η b δB ρB (n + 4)
  let Lg := Ag * Cg ^ (n + 4) * ((n + 4 : ℕ) : ℝ) ^ (2 * (j + 1))
  have hLg : 0 ≤ Lg := by dsimp [Lg]; positivity
  have hsupport : ∀ θ ∈ tsupport g, ∀ k, θ k ∈ Icc (-b - βC) βC := by
    intro θ ht k
    have hh := compactRightProduct_weighted_tsupport hcut
      (fun y : Fin (n + 4) → ℝ => (lowerPopulationCutoff η y : ℂ)) ht k
    exact ⟨by linarith [hh.1, hδB.trans hbC], hh.2.trans (hρB.trans hbC)⟩
  have hresult := hbound n R hR (by omega) g Lg hLg
    (actualLowerCompactRightCutoff_contDiff η b δB ρB (n + 4))
    (hgjet (n + 4) (by omega)) hsupport σ hσ τ ⟨hτ.1, hτ.2.trans hdC⟩ ξ hξ μ ε
    ⟨hε.1, hε.2.trans_le hdC⟩
  rw [hcard, rightCurrentCoareaEnvelope_cutoff] at hresult
  exact hresult

end
end IsingBulk.AnisoF002.Isotropic
