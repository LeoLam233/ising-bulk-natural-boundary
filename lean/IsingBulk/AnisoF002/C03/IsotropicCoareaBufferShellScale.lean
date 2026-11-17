import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferSignedShell

/-!
# The complete physical shell Delta power with independent angular width
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric MeasureTheory Filter

theorem exists_actual_signed_shell_delta_bound_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ K : ℝ, 0 < δ ∧ δ ≤ β ∧ 1 ≤ K ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ μ r : ℝ, 0 < r →
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
        (∫ x in actualCenteredShell (n + 2) (μ - b) b β r,
          actualSignedFullDensity (isotropicRadialParameter α ε) σ η τ ξ
            (centeredConstraintAngles (μ - b) x)) ≤
          K ^ (n + 3) * (n + 3) ^ 3 *
            (r / Real.sqrt (|μ| + r + ε)) ^ n * (1 + |Real.log ε|) := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_complete_signed_shell_coarea_buffer α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, C, W, hδ, hδβ, hC, hW, hbound⟩ := hdata η hη hwidth
  have hδ1 : δ ≤ 1 := hδβ.trans hβ1
  let K := max 1 (max C (24 * W))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) hK1
  have hCK : C ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hAK : 24 * W ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ, K, hδ, hδβ, hK1, ?_⟩
  intro n ε hε hεδ τ ξ hτ hξ μ r hr σ hσ
  have hmain := hbound (n + 1) ε hε hεδ τ ξ hτ hξ μ r hr σ hσ
  have heN : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
  simp only [heN] at hmain
  rw [shell_scale_power_identity n C (24 * W) _ μ r ε _ hr hε] at hmain
  have hp : C * (24 * W) ^ (n + 1) ≤ K ^ (n + 3) := by
    calc
      _ ≤ K * K ^ (n + 1) := mul_le_mul hCK (pow_le_pow_left₀ (by positivity) hAK _)
        (by positivity) hK.le
      _ = K ^ (n + 2) := by rw [pow_succ K (n + 1)]; ring
      _ ≤ K ^ (n + 3) := by
        rw [pow_succ K (n + 2)]
        exact le_mul_of_one_le_right (by positivity) hK1
  exact hmain.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity))
    (by positivity))

end IsingBulk.AnisoF002.Isotropic
