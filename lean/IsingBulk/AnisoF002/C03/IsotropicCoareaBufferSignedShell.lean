import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferShell
import IsingBulk.AnisoF002.C03.IsotropicShellScaleBound

/-!
# Both complete physical signs on the fixed angular shell
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric MeasureTheory Filter

theorem exists_actual_complete_signed_shell_coarea_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ C W : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < C ∧ 0 < W ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ μ r : ℝ, 0 < r →
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
        (∫ x in actualCenteredShell (n + 1) (μ - b) b β r,
          actualSignedFullDensity (isotropicRadialParameter α ε) σ η τ ξ
            (centeredConstraintAngles (μ - b) x)) ≤
          (C * (n + 2) ^ 3 * Real.sqrt (|μ| + r + ε) / r * (1 + |Real.log ε|)) *
            (24 * W * r / Real.sqrt (|μ| + r + ε)) ^ n := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_complete_shell_coarea_buffer α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, C, W, hδ, hδβ, hC, hW, hbound⟩ := hdata η hη hwidth
  have hδ1 : δ ≤ 1 := hδβ.trans hβ1
  refine ⟨δ, C, W, hδ, hδβ, hC, hW, ?_⟩
  intro n ε hε hεδ τ ξ hτ hξ μ r hr σ hσ
  rcases hσ with rfl | rfl
  · simpa only [actualFullPhaseDensity_zero_eq_signed] using hbound n ε hε hεδ τ ξ hτ hξ μ r 0 hr
  · simpa only [actualFullPhaseDensity_pi_eq_signed] using hbound n ε hε hεδ τ ξ hτ hξ μ r Real.pi hr

end IsingBulk.AnisoF002.Isotropic
