import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferFullRight
import IsingBulk.AnisoF002.C03.IsotropicAllMeanCoarea

/-!
# Complete actual right coarea with angular geometry before bump width and time
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric MeasureTheory Filter

theorem exists_actual_all_mean_right_coarea_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ K : ℝ, 0 < δ ∧ δ ≤ β ∧ 1 ≤ K ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ a : ℝ,
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
        (∑ l ∈ admissibleRightLifts (n + 4) b β a,
          ∫ x in actualCenteredRightDomain (n + 3) (constrainedRightMean (n + 4) b a l - b) b β,
            actualSignedFullDensity (isotropicRadialParameter α ε) σ η τ ξ
              (centeredConstraintAngles (constrainedRightMean (n + 4) b a l - b) x)) ≤
          4 * K ^ (n + 4) * (n + 4) ^ 4 * (1 + |Real.log ε|) := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_full_right_coarea_buffer α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, K, hδ, hδβ, hK, hbound⟩ := hdata η hη hwidth
  have hδ1 : δ ≤ 1 := hδβ.trans hβ1
  refine ⟨δ, K, hδ, hδβ, hK, ?_⟩
  intro n ε hε hεδ τ ξ hτ hξ a σ hσ
  have hsum := Finset.sum_le_sum (s := admissibleRightLifts (n + 4) b β a)
    (fun l _ => hbound n ε hε hεδ τ ξ hτ hξ (constrainedRightMean (n + 4) b a l) σ hσ)
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : ((admissibleRightLifts (n + 4) b β a).card : ℝ) ≤ (n + 4 : ℝ) := by
    exact_mod_cast admissibleRightLifts_card_le (n + 4) (by omega) b β a hb.2 hβ1
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hh := mul_le_mul_of_nonneg_right hc
    (by positivity : 0 ≤ 4 * K ^ (n + 4) * (n + 4) ^ 3 * (1 + |Real.log ε|))
  exact hsum.trans (hh.trans_eq (by ring))

end IsingBulk.AnisoF002.Isotropic
