import IsingBulk.AnisoF002.C03.NegativeSelectionEndpoints
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The literal integer interval for negative-HT order selection

Both endpoints are natural-number floors.  Their actual rounding errors
are included in the sign test, and first crossing is selected entirely
inside the integer interval.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

def selectionStart (n : ℕ) : ℕ := ⌊(n : ℝ) ^ 2 * Real.log (n : ℝ) / 2⌋₊
def selectionFinish (n : ℕ) : ℕ := ⌊3 * (n : ℝ) ^ 2 * Real.log (n : ℝ) / 2⌋₊

theorem selection_integer_endpoint_bounds {n : ℕ} (hn : 1 ≤ n)
    (ht : 256 ≤ Real.log (n : ℝ)) :
    (n : ℝ) ^ 2 * Real.log (n : ℝ) / 3 ≤ (selectionStart n : ℝ) ∧
    (selectionStart n : ℝ) ≤ (n : ℝ) ^ 2 * Real.log (n : ℝ) / 2 ∧
    5 * (n : ℝ) ^ 2 * Real.log (n : ℝ) / 4 ≤ (selectionFinish n : ℝ) ∧
    (selectionFinish n : ℝ) ≤ 3 * (n : ℝ) ^ 2 * Real.log (n : ℝ) / 2 ∧
    selectionStart n ≤ selectionFinish n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have ht0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hA : 256 ≤ (n : ℝ) ^ 2 * Real.log (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hn2 ht0
    nlinarith
  have hstartLo := Nat.lt_floor_add_one ((n : ℝ) ^ 2 * Real.log (n : ℝ) / 2)
  have hstartHi := Nat.floor_le (show 0 ≤ (n : ℝ) ^ 2 * Real.log (n : ℝ) / 2 by positivity)
  have hfinishLo := Nat.lt_floor_add_one (3 * (n : ℝ) ^ 2 * Real.log (n : ℝ) / 2)
  have hfinishHi := Nat.floor_le (show 0 ≤ 3 * (n : ℝ) ^ 2 * Real.log (n : ℝ) / 2 by positivity)
  change _ < (selectionStart n : ℝ) + 1 at hstartLo
  change (selectionStart n : ℝ) ≤ _ at hstartHi
  change _ < (selectionFinish n : ℝ) + 1 at hfinishLo
  change (selectionFinish n : ℝ) ≤ _ at hfinishHi
  refine ⟨by linarith, hstartHi, by linarith, hfinishHi, ?_⟩
  unfold selectionStart selectionFinish
  exact Nat.floor_mono (by linarith)

theorem exists_integer_window_crossing (F : ℕ → ℝ) {n : ℕ} {C d δ : ℝ}
    (hn : 1 ≤ n) (ht : 256 ≤ Real.log (n : ℝ)) (hC : 0 ≤ C) (hd : 0 < d)
    (hlarge : 32 * (C + 1) ≤ Real.log (n : ℝ))
    (hstart : |F (selectionStart n) / (2 * d) -
      (2 * (selectionStart n : ℝ) / n - (n : ℝ) * Real.log (selectionStart n : ℝ))| ≤
      C * ((n : ℝ) + (n : ℝ) ^ 3 / (selectionStart n : ℝ) +
        (selectionStart n : ℝ) / (n : ℝ) ^ 3))
    (hfinish : |F (selectionFinish n) / (2 * d) -
      (2 * (selectionFinish n : ℝ) / n - (n : ℝ) * Real.log (selectionFinish n : ℝ))| ≤
      C * ((n : ℝ) + (n : ℝ) ^ 3 / (selectionFinish n : ℝ) +
        (selectionFinish n : ℝ) / (n : ℝ) ^ 3))
    (hstep : ∀ j : ℕ, selectionStart n ≤ j → j < selectionFinish n →
      F (j + 1) - F j ≤ δ) :
    ∃ j : ℕ, selectionStart n < j ∧ j ≤ selectionFinish n ∧
      0 ≤ F j ∧ F j ≤ δ ∧
      (n : ℝ) ^ 2 * Real.log (n : ℝ) / 3 ≤ (j : ℝ) ∧
      (j : ℝ) ≤ 3 * (n : ℝ) ^ 2 * Real.log (n : ℝ) / 2 := by
  obtain ⟨hslo, hshi, hflo, hfhi, hsf⟩ := selection_integer_endpoint_bounds hn ht
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hneg := controlled_crossing_lower_negative hnR ht hC hd hlarge hslo hshi hstart
  have hpos := controlled_crossing_upper_positive hnR ht hC hd hlarge hflo hfhi hfinish
  obtain ⟨j, hjlo, hjhi, hj0, hjδ⟩ :=
    exists_small_nonnegative_crossing F _ _ δ hsf hneg hpos.le hstep
  refine ⟨j, hjlo, hjhi, hj0, hjδ, ?_, ?_⟩
  · exact hslo.trans (by exact_mod_cast hjlo.le)
  · exact (show (j : ℝ) ≤ selectionFinish n by exact_mod_cast hjhi).trans hfhi

end
end IsingBulk.AnisoF002.NegativeHT
