import IsingBulk.AnisoF002.C03.IsotropicCountableCoarea
import IsingBulk.AnisoF002.C03.IsotropicConstrainedMeans

/-!
# The complete finite sum over all admissible constrained means

The actual angular sum determines each mean lift. The exact integer
interval contains every nonempty right chart and at most N integers.
The complete coarea integral consequently costs only one additional
particle factor; no winding or sign is selected away.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Filter Metric MeasureTheory

theorem actual_right_mean_lift_mem (d : ℕ) (b δ a : ℝ) (l : ℤ)
    (hcell : (actualCenteredRightDomain d (constrainedRightMean (d + 1) b a l - b) b δ).Nonempty) :
    l ∈ admissibleRightLifts (d + 1) b δ a := by
  obtain ⟨x, hx⟩ := hcell
  have hN : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsum : (∑ k, centeredConstraintAngles (constrainedRightMean (d + 1) b a l - b) x k) =
      2 * Real.pi * l + a := by
    rw [centeredConstraintAngles_sum]
    simp only [constrainedRightMean, add_sub_cancel_left]
    push_cast at hN ⊢
    field_simp
  have hlo := Finset.sum_le_sum (fun (k : Fin (d + 1)) (_ : k ∈ Finset.univ) => (hx k).1)
  have hup := Finset.sum_le_sum (fun (k : Fin (d + 1)) (_ : k ∈ Finset.univ) => (hx k).2)
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlo hup
  exact (admissibleRightLifts_mem_iff (d + 1) b δ a l).mpr ⟨hlo, hup⟩

theorem actual_right_empty_off_admissible_lifts (d : ℕ) (b δ a : ℝ) (l : ℤ)
    (hl : l ∉ admissibleRightLifts (d + 1) b δ a) :
    actualCenteredRightDomain d (constrainedRightMean (d + 1) b a l - b) b δ = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  exact fun h => hl (actual_right_mean_lift_mem d b δ a l h)

/-- Every full right chart, every mean lift and both physical signs
are included in a single bound uniform over all N >= 4. -/
theorem exists_actual_all_mean_right_coarea (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ K ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ a : ℝ,
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
        (∑ l ∈ admissibleRightLifts (n + 4) b δ a,
          ∫ x in actualCenteredRightDomain (n + 3) (constrainedRightMean (n + 4) b a l - b) b δ,
            actualSignedFullDensity (isotropicRadialParameter α ε) σ η τ ξ
              (centeredConstraintAngles (constrainedRightMean (n + 4) b a l - b) x)) ≤
          4 * K ^ (n + 4) * (n + 4) ^ 4 * (1 + |Real.log ε|) := by
  obtain ⟨δ, K, hδ, hδ1, hK, hbound⟩ :=
    exists_actual_full_right_coarea α b η hα hb hpoint hη hwidth
  refine ⟨δ, K, hδ, hδ1, hK, ?_⟩
  intro n ε hε hεδ τ ξ hτ hξ a σ hσ
  have hsum := Finset.sum_le_sum (s := admissibleRightLifts (n + 4) b δ a)
    (fun l _ => hbound n ε hε hεδ τ ξ hτ hξ (constrainedRightMean (n + 4) b a l) σ hσ)
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : ((admissibleRightLifts (n + 4) b δ a).card : ℝ) ≤ (n + 4 : ℝ) := by
    exact_mod_cast admissibleRightLifts_card_le (n + 4) (by omega) b δ a hb.2 hδ1
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hh := mul_le_mul_of_nonneg_right hc
    (by positivity : 0 ≤ 4 * K ^ (n + 4) * (n + 4) ^ 3 * (1 + |Real.log ε|))
  exact hsum.trans (hh.trans_eq (by ring))

end IsingBulk.AnisoF002.Isotropic
