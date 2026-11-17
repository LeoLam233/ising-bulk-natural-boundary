import IsingBulk.AnisoF002.C03.NegativeMiddleErrorScales
import IsingBulk.AnisoF002.NegativeHT.SeriesNoncancellation

/-!
# Quantitative full-series assembly after every particle range is bounded

All physical residue terms outside the complete finite middle window stay
in the infinite sum.  The common attachment phase has modulus one; model
competitors themselves may have arbitrary phases.  This is an assembly
lemma whose actual range estimates are supplied by the physical chain.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open scoped BigOperators Classical

theorem finite_model_attachment_error_bound (P M : ℕ → ℂ) (S : Finset ℕ)
    (q : ℕ) (hq : q ∈ S) (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (hcompetitors : (∑ k ∈ S.erase q, ‖M k‖) ≤ ‖M q‖ / 16)
    (herror : ∀ k ∈ S, ‖P k - ζ * M k‖ ≤ ‖M k‖ / 16) :
    ‖(∑ k ∈ S, P k) - ζ * M q‖ ≤ ‖M q‖ / 4 := by
  have hMsum := Finset.sum_erase_add (s := S) (f := fun k => ‖M k‖) hq
  have hMbound : (∑ k ∈ S, ‖M k‖) ≤ 17 / 16 * ‖M q‖ := by linarith
  have he : ‖∑ k ∈ S, (P k - ζ * M k)‖ ≤ 17 / 256 * ‖M q‖ := by
    calc
      _ ≤ ∑ k ∈ S, ‖P k - ζ * M k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ S, ‖M k‖ / 16 := Finset.sum_le_sum herror
      _ = (∑ k ∈ S, ‖M k‖) / 16 := by rw [Finset.sum_div]
      _ ≤ _ := by linarith
  have hm : ‖ζ * ∑ k ∈ S.erase q, M k‖ ≤ ‖M q‖ / 16 := by
    rw [norm_mul, hζ, one_mul]
    exact (norm_sum_le _ _).trans hcompetitors
  have hMidentity := Finset.sum_erase_add (s := S) (f := M) hq
  have hid : (∑ k ∈ S, P k) - ζ * M q =
      (∑ k ∈ S, (P k - ζ * M k)) + ζ * ∑ k ∈ S.erase q, M k := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hMidentity]
    ring
  rw [hid]
  have hh := norm_add_le (∑ k ∈ S, (P k - ζ * M k)) (ζ * ∑ k ∈ S.erase q, M k)
  nlinarith [norm_nonneg (M q)]

theorem complete_residue_series_half_lower_bound (P M : ℕ → ℂ)
    (S : Finset ℕ) (q : ℕ) (hq : q ∈ S) (ζ rem : ℂ) (E : ℝ)
    (hP : Summable fun n => ‖P n‖) (hζ : ‖ζ‖ = 1)
    (hmain : E ≤ ‖M q‖)
    (hcompetitors : (∑ k ∈ S.erase q, ‖M k‖) ≤ ‖M q‖ / 16)
    (herror : ∀ k ∈ S, ‖P k - ζ * M k‖ ≤ ‖M k‖ / 16)
    (houtside : (∑' n : ℕ, ‖if n ∈ S then (0 : ℂ) else P n‖) ≤ 3 * E / 64)
    (hrem : ‖rem‖ ≤ E / 64) :
    E / 2 ≤ ‖(∑' n : ℕ, P n) + rem‖ := by
  let U : ℕ → ℂ := fun n => if n ∈ S then P n else 0
  let V : ℕ → ℂ := fun n => if n ∈ S then 0 else P n
  have hUN : Summable (fun n => ‖U n‖) :=
    hP.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by dsimp [U]; split_ifs <;> simp)
  have hVN : Summable (fun n => ‖V n‖) :=
    hP.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by dsimp [V]; split_ifs <;> simp)
  have hsumU : (∑' n : ℕ, U n) = ∑ n ∈ S, P n := by
    calc
      _ = ∑ n ∈ S, U n := tsum_eq_sum (fun n hn => by simp [U, hn])
      _ = _ := Finset.sum_congr rfl (fun n hn => by simp [U, hn])
  have hsplit : (∑' n : ℕ, P n) = (∑ n ∈ S, P n) + ∑' n : ℕ, V n := by
    calc
      _ = (∑' n : ℕ, (U n + V n)) := by
        apply tsum_congr
        intro n
        by_cases hn : n ∈ S <;> simp [U, V, hn]
      _ = (∑' n : ℕ, U n) + ∑' n : ℕ, V n := hUN.of_norm.tsum_add hVN.of_norm
      _ = _ := by rw [hsumU]
  have htail : ‖∑' n : ℕ, V n‖ ≤ 3 * E / 64 :=
    (norm_tsum_le_tsum_norm hVN).trans houtside
  have hfinite := finite_model_attachment_error_bound P M S q hq ζ hζ hcompetitors herror
  have hid : ((∑' n : ℕ, P n) + rem) - ζ * M q =
      (((∑ n ∈ S, P n) - ζ * M q) + ∑' n : ℕ, V n) + rem := by
    rw [hsplit]
    ring
  have herr : ‖((∑' n : ℕ, P n) + rem) - ζ * M q‖ ≤ ‖M q‖ / 4 + E / 16 := by
    rw [hid]
    have h1 := norm_add_le ((∑ n ∈ S, P n) - ζ * M q) (∑' n : ℕ, V n)
    have h2 := norm_add_le (((∑ n ∈ S, P n) - ζ * M q) + ∑' n : ℕ, V n) rem
    linarith
  have hrev := norm_sub_norm_le (ζ * M q) ((∑' n : ℕ, P n) + rem)
  rw [norm_mul, hζ, one_mul, norm_sub_rev] at hrev
  have hE : 0 ≤ E := by have hh := norm_nonneg rem; linarith
  linarith

end
end IsingBulk.AnisoF002.NegativeHT
