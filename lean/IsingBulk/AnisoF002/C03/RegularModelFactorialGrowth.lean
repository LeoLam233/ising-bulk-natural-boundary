import IsingBulk.AnisoF002.C03.RegularModelFactorials

/-!
# Uniform pointwise logarithm of the exact factorial product

The comparison is a finite sum of explicit factorial inequalities.  The
logarithmic integral approximation is replaced by the elementary bound
r*log(n/r) <= n-r, so no unproved Stirling error is differentiated.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open scoped BigOperators

theorem model_sum_range_cast (n : ℕ) :
    (∑ r ∈ Finset.range n, (r : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem model_factorial_at_larger_scale (n r : ℕ) (hrn : r ≤ n) :
    |Real.log (r.factorial : ℝ) - (r : ℝ) * Real.log n| ≤ n := by
  by_cases hr : r = 0
  · subst r
    simp only [Nat.factorial_zero, Nat.cast_one, Real.log_one, Nat.cast_zero, zero_mul,
      sub_self, abs_zero]
    exact Nat.cast_nonneg _
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hrpos
  have hnr : 0 ≤ (n : ℝ) - r := sub_nonneg.mpr (by exact_mod_cast hrn)
  have hi := log_increment_bounds hrR hnr
  rw [add_sub_cancel] at hi
  have hc : (r : ℝ) * (Real.log n - Real.log r) ≤ (n : ℝ) - r := by
    have hh := (le_div_iff₀ hrR).mp hi.2
    nlinarith
  have hfac := model_log_factorial_error r hrpos
  calc
    _ = |(Real.log (r.factorial : ℝ) - (r : ℝ) * Real.log r) -
        (r : ℝ) * (Real.log n - Real.log r)| := by congr 1; ring
    _ ≤ |Real.log (r.factorial : ℝ) - (r : ℝ) * Real.log r| +
        |(r : ℝ) * (Real.log n - Real.log r)| := abs_sub _ _
    _ ≤ (r : ℝ) + ((n : ℝ) - r) := by
      rw [abs_of_nonneg (mul_nonneg hrR.le hi.1)]
      exact add_le_add hfac hc
    _ = _ := by ring

theorem actual_factorial_log_growth (n : ℕ) (hn : 0 < n) :
    |Real.log (factorialProduct n) - (n : ℝ) ^ 2 / 2 * Real.log n| ≤
      (2 + Real.log 2) * (n : ℝ) ^ 2 := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlognU : Real.log n ≤ (n : ℝ) :=
    (Real.log_le_sub_one_of_pos (by exact_mod_cast hn)).trans (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsum : Real.log (factorialProduct n) =
      ∑ r ∈ Finset.range n, (Real.log (r.factorial : ℝ) - (r : ℝ) * Real.log 2) := by
    have hh := block_difference (fun k => Real.log (factorialProduct k)) 0 n
    have hzero : Real.log (factorialProduct 0) = 0 := by simp [factorialProduct]
    simp only [Nat.zero_add, hzero, sub_zero] at hh
    simp_rw [log_factorialProduct_step] at hh
    exact hh
  let D : ℕ → ℝ := fun r => Real.log (r.factorial : ℝ) - (r : ℝ) * Real.log n - (r : ℝ) * Real.log 2
  have hterm (r : ℕ) (hr : r ∈ Finset.range n) : |D r| ≤ (n : ℝ) * (1 + Real.log 2) := by
    have hrn : r ≤ n := (Finset.mem_range.mp hr).le
    have hrR : (r : ℝ) ≤ n := by exact_mod_cast hrn
    have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    calc
      _ ≤ |Real.log (r.factorial : ℝ) - (r : ℝ) * Real.log n| + |(r : ℝ) * Real.log 2| := abs_sub _ _
      _ ≤ (n : ℝ) + (n : ℝ) * Real.log 2 := by
        rw [abs_of_nonneg (mul_nonneg hr0 hlog2)]
        exact add_le_add (model_factorial_at_larger_scale n r hrn)
          (mul_le_mul_of_nonneg_right hrR hlog2)
      _ = _ := by ring
  have hsumD : |∑ r ∈ Finset.range n, D r| ≤ (n : ℝ) ^ 2 * (1 + Real.log 2) := by
    calc
      _ ≤ ∑ r ∈ Finset.range n, |D r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r ∈ Finset.range n, (n : ℝ) * (1 + Real.log 2) := Finset.sum_le_sum hterm
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hid : Real.log (factorialProduct n) - (n : ℝ) ^ 2 / 2 * Real.log n =
      (∑ r ∈ Finset.range n, D r) - (n : ℝ) / 2 * Real.log n := by
    rw [hsum]
    dsimp [D]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, model_sum_range_cast]
    ring
  rw [hid]
  calc
    _ ≤ |∑ r ∈ Finset.range n, D r| + |(n : ℝ) / 2 * Real.log n| := abs_sub _ _
    _ ≤ (n : ℝ) ^ 2 * (1 + Real.log 2) + (n : ℝ) ^ 2 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) / 2 * Real.log n)]
      apply add_le_add hsumD
      have hh := mul_le_mul_of_nonneg_left hlognU (show 0 ≤ (n : ℝ) / 2 by positivity)
      nlinarith [sq_nonneg (n : ℝ)]
    _ = _ := by ring

end
end IsingBulk.AnisoF002.NegativeHT
