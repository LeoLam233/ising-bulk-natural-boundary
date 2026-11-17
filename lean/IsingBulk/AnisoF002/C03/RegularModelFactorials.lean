import IsingBulk.AnisoF002.NegativeHT.FactorialRectangle
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Centered estimates for the actual finite factorial product

The first difference uses an elementary explicit logarithmic factorial
bound; the second difference uses the exact finite rectangle already
proved in F002.  No differentiated asymptotic expression is used.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open scoped BigOperators

theorem model_log_factorial_error (n : ℕ) (hn : 0 < n) :
    |Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log n| ≤ n := by
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlo := Stirling.le_log_factorial_stirling (Nat.ne_of_gt hn)
  have hlog := Real.log_nonneg hn1
  have hπ : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.one_le_pi_div_two])
  have hpow : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hhi := Real.log_le_log (show 0 < (n.factorial : ℝ) by positivity) hpow
  rw [Real.log_pow] at hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem model_log_lipschitz_one {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
  by_cases hxy : y ≤ x
  · have hh := log_increment_bounds hy0 (sub_nonneg.mpr hxy)
    rw [add_sub_cancel] at hh
    rw [abs_of_nonneg hh.1, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact hh.2.trans (div_le_self (sub_nonneg.mpr hxy) hy)
  · have hyx := le_of_lt (lt_of_not_ge hxy)
    have hh := log_increment_bounds hx0 (sub_nonneg.mpr hyx)
    rw [add_sub_cancel] at hh
    rw [abs_sub_comm, abs_of_nonneg hh.1, abs_sub_comm x y,
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hh.2.trans (div_le_self (sub_nonneg.mpr hyx) hx)

theorem model_xlogx_center_error {m x d : ℝ} (hm : 1 ≤ m) (hx : 1 ≤ x)
    (hmx : m ≤ 2 * x) (hd : 0 ≤ d) (hclose : |m - x| ≤ d) :
    |m * Real.log m - x * Real.log x| ≤ 3 * d * x := by
  have hlog : |Real.log m| ≤ 2 * x := by
    rw [abs_of_nonneg (Real.log_nonneg hm)]
    exact (Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num) hm)).trans (by linarith)
  calc
    _ = |(m - x) * Real.log m + x * (Real.log m - Real.log x)| := by congr 1; ring
    _ ≤ |(m - x) * Real.log m| + |x * (Real.log m - Real.log x)| := abs_add_le _ _
    _ = |m - x| * |Real.log m| + x * |Real.log m - Real.log x| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ x)]
    _ ≤ d * (2 * x) + x * d := add_le_add
      (mul_le_mul hclose hlog (abs_nonneg _) hd)
      (mul_le_mul_of_nonneg_left ((model_log_lipschitz_one hm hx).trans hclose) (by linarith))
    _ = _ := by ring

theorem actual_factorial_first_difference (n d : ℕ) (hn : 0 < n) :
    |Real.log (factorialProduct (n + 2 * d)) - Real.log (factorialProduct n) -
      2 * (d : ℝ) * ((n : ℝ) + d) * Real.log ((n : ℝ) + d)| ≤
        2 * (d : ℝ) * (2 + 3 * (d : ℝ) + 2 * Real.log 2) * ((n : ℝ) + d) := by
  let x : ℝ := (n : ℝ) + d
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hx1 : 1 ≤ x := by dsimp [x]; linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hterm (i : ℕ) (hi : i ∈ Finset.range (2 * d)) :
      |Real.log ((n + i).factorial : ℝ) - ((n + i : ℕ) : ℝ) * Real.log 2 -
        x * Real.log x| ≤ (2 + 3 * (d : ℝ) + 2 * Real.log 2) * x := by
    have hiR : (i : ℝ) < 2 * d := by exact_mod_cast Finset.mem_range.mp hi
    have hm1 : 1 ≤ ((n + i : ℕ) : ℝ) := by push_cast; linarith [show (0 : ℝ) ≤ i from Nat.cast_nonneg i]
    have hmx : ((n + i : ℕ) : ℝ) ≤ 2 * x := by dsimp [x]; push_cast; linarith
    have hclose : |((n + i : ℕ) : ℝ) - x| ≤ d := by
      apply abs_le.mpr
      dsimp [x]
      push_cast
      constructor <;> linarith [show (0 : ℝ) ≤ i from Nat.cast_nonneg i]
    have hfac := model_log_factorial_error (n + i) (by omega)
    have hcenter := model_xlogx_center_error hm1 hx1 hmx hd0 hclose
    let m : ℝ := n + i
    calc
      _ = |(Real.log ((n + i).factorial : ℝ) - m * Real.log m) +
          (m * Real.log m - x * Real.log x) - m * Real.log 2| := by
        dsimp [m]; push_cast; congr 1; ring
      _ ≤ |Real.log ((n + i).factorial : ℝ) - m * Real.log m| +
          |m * Real.log m - x * Real.log x| + |m * Real.log 2| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ m + 3 * (d : ℝ) * x + m * Real.log 2 := by
        have hm0 : 0 ≤ m := by dsimp [m]; positivity
        rw [abs_mul, abs_of_nonneg hm0, abs_of_nonneg hlog2]
        exact add_le_add (add_le_add (by simpa [m] using hfac) (by simpa [m] using hcenter)) le_rfl
      _ ≤ 2 * x + 3 * (d : ℝ) * x + (2 * x) * Real.log 2 :=
        add_le_add (add_le_add (by simpa [m] using hmx) le_rfl)
          (mul_le_mul_of_nonneg_right (by simpa [m] using hmx) hlog2)
      _ = _ := by ring
  rw [block_difference (fun k => Real.log (factorialProduct k)) n (2 * d)]
  simp_rw [log_factorialProduct_step]
  have hconst : 2 * (d : ℝ) * x * Real.log x =
      ∑ i ∈ Finset.range (2 * d), x * Real.log x := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    ring
  change |(∑ i ∈ Finset.range (2 * d), _) - 2 * (d : ℝ) * x * Real.log x| ≤ _
  rw [hconst, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range (2 * d), |Real.log ((n + i).factorial : ℝ) -
        ((n + i : ℕ) : ℝ) * Real.log 2 - x * Real.log x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (2 * d), (2 + 3 * (d : ℝ) + 2 * Real.log 2) * x :=
      Finset.sum_le_sum hterm
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      ring

theorem actual_factorial_second_difference (n d : ℕ) (hn : 0 < n) :
    |Real.log (factorialProduct (n + 2 * d)) - 2 * Real.log (factorialProduct (n + d)) +
      Real.log (factorialProduct n) - (d : ℝ) ^ 2 * Real.log ((n : ℝ) + d)| ≤
        (d : ℝ) ^ 2 * Real.log 2 + 3 * (d : ℝ) ^ 3 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hrect := log_factorialProduct_rectangle_remainder n d hn
  dsimp only at hrect
  have hlog := log_increment_bounds hnR hd0
  let D := Real.log (factorialProduct (n + 2 * d)) - 2 * Real.log (factorialProduct (n + d)) +
    Real.log (factorialProduct n)
  have hrect' : |D - (d : ℝ) ^ 2 * (Real.log n - Real.log 2)| ≤ 2 * (d : ℝ) ^ 3 / n := by
    rw [abs_of_nonneg hrect.1]
    exact hrect.2
  have hl : |Real.log ((n : ℝ) + d) - Real.log n| ≤ (d : ℝ) / n := by
    rw [abs_of_nonneg hlog.1]
    exact hlog.2
  calc
    _ = |(D - (d : ℝ) ^ 2 * (Real.log n - Real.log 2)) -
        (d : ℝ) ^ 2 * (Real.log ((n : ℝ) + d) - Real.log n) - (d : ℝ) ^ 2 * Real.log 2| := by
      dsimp [D]; congr 1; ring
    _ ≤ |D - (d : ℝ) ^ 2 * (Real.log n - Real.log 2)| +
        |(d : ℝ) ^ 2 * (Real.log ((n : ℝ) + d) - Real.log n)| + |(d : ℝ) ^ 2 * Real.log 2| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 2 * (d : ℝ) ^ 3 / n + (d : ℝ) ^ 2 * ((d : ℝ) / n) + (d : ℝ) ^ 2 * Real.log 2 := by
      simp only [abs_mul, abs_of_nonneg (sq_nonneg (d : ℝ)), abs_of_nonneg hlog2]
      exact add_le_add (add_le_add hrect' (mul_le_mul_of_nonneg_left hl (sq_nonneg _))) le_rfl
    _ = (d : ℝ) ^ 2 * Real.log 2 + 3 * (d : ℝ) ^ 3 / n := by ring
    _ ≤ _ := add_le_add le_rfl (div_le_self (by positivity) hn1)

end
end IsingBulk.AnisoF002.NegativeHT
