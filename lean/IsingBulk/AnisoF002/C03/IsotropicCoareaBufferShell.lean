import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferCell
import IsingBulk.AnisoF002.C03.IsotropicCompleteShellCoarea

/-!
# Every actual extreme cell in the fixed angular shell
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric MeasureTheory Filter

theorem exists_actual_complete_shell_coarea_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ C W : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < C ∧ 0 < W ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ μ r γ : ℝ, 0 < r →
        (∫ x in actualCenteredShell (n + 1) (μ - b) b β r,
          actualFullPhaseDensity (isotropicRadialParameter α ε) η τ ξ γ
            (centeredConstraintAngles (μ - b) x)) ≤
          (C * (n + 2) ^ 3 * Real.sqrt (|μ| + r + ε) / r * (1 + |Real.log ε|)) *
            (24 * W * r / Real.sqrt (|μ| + r + ε)) ^ n := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_extreme_cell_coarea_buffer α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, C, W, hδ, hδβ, hC, hW, hbound⟩ := hdata η hη hwidth
  have hδ1 : δ ≤ 1 := hδβ.trans hβ1
  refine ⟨δ, C, W, hδ, hδβ, hC, hW, ?_⟩
  intro n ε hε hεδ τ ξ hτ hξ μ r γ hr
  let s := isotropicRadialParameter α ε
  let B := (C * (n + 2) * Real.sqrt (|μ| + r + ε) / r * (1 + |Real.log ε|)) *
    (24 * W * r / Real.sqrt (|μ| + r + ε)) ^ n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs : 0 < s.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  have hcell (i j : Fin (n + 2)) :
      (∫ x in centeredExtremeCell (μ - b) b β r i j,
        actualFullPhaseDensity s η τ ξ γ (centeredConstraintAngles (μ - b) x)) ≤ B := by
    by_cases hij : i = j
    · subst j
      rw [centeredExtremeCell_diagonal_empty _ _ _ _ hr, Measure.restrict_empty, integral_zero_measure]
      exact hB
    · obtain ⟨σ, hσ0, hσlast⟩ := exists_perm_first_last n i j hij
      rw [← hσ0, ← hσlast, centeredExtremeCell_permutation_integral σ,
        centeredParameterChart_cell_integral]
      exact hbound n ε hε hεδ τ ξ hτ hξ μ r γ hr
  have hmain := (actualCenteredShell_integral_le_cells (n + 1) (μ - b) b β r s hs η τ ξ γ hη hτ.1 hξ.1).trans
    (Finset.sum_le_sum (fun ij _ => hcell ij.1 ij.2))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hmain
  exact hmain.trans_eq (by dsimp [B]; ring)

end IsingBulk.AnisoF002.Isotropic
