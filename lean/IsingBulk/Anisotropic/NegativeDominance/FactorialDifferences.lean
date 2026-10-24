import IsingBulk.Anisotropic.NegativeDominance.ExactModel

/-! Exact discrete factorial differences underlying (5.28). -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

/-- A single logarithmic increment of the exact Mehta factorial product. -/
theorem log_factorialProduct_succ (n : ℕ) :
    Real.log (factorialProduct (n + 1)) = Real.log (factorialProduct n) +
      Real.log (n.factorial : ℝ) - n * Real.log 2 := by
  rw [factorialProduct_succ,
    Real.log_div (mul_ne_zero (factorialProduct_ne_zero n) (by positivity)) (by positivity),
    Real.log_mul (factorialProduct_ne_zero n) (by positivity), Real.log_pow]

/-- The exact unit second difference, valid at every natural index. -/
theorem log_factorialProduct_second_difference (n : ℕ) :
    Real.log (factorialProduct (n + 2)) - 2 * Real.log (factorialProduct (n + 1)) +
      Real.log (factorialProduct n) = Real.log ((n : ℝ) + 1) - Real.log 2 := by
  have h1 := log_factorialProduct_succ n
  have h2 := log_factorialProduct_succ (n + 1)
  have hf : Real.log ((n + 1).factorial : ℝ) =
      Real.log ((n : ℝ) + 1) + Real.log (n.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Real.log_mul (by positivity) (by positivity)]
  rw [hf] at h2
  push_cast at h2
  linarith

/-- An arbitrary-step second difference is the exact rectangular sum of
unit second differences. This is an algebraic identity, not an estimate
obtained by differentiating an asymptotic error. -/
theorem second_difference_rectangle (f : ℕ → ℝ) (n d : ℕ) :
    f (n + 2 * d) - 2 * f (n + d) + f n =
      ∑ k ∈ Finset.range d, ∑ l ∈ Finset.range d,
        (f (n + k + l + 2) - 2 * f (n + k + l + 1) + f (n + k + l)) := by
  have hi (k : ℕ) :
      (∑ l ∈ Finset.range d,
        (f (n + k + l + 2) - 2 * f (n + k + l + 1) + f (n + k + l))) =
      (f (n + k + d + 1) - f (n + k + d)) -
        (f (n + k + 1) - f (n + k)) := by
    convert Finset.sum_range_sub (fun l => f (n + k + l + 1) - f (n + k + l)) d using 1
    · apply Finset.sum_congr rfl
      intro l _
      simp only [Nat.add_assoc]
      ring
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  have ha := Finset.sum_range_sub (fun k => f (n + d + k)) d
  have hb := Finset.sum_range_sub (fun k => f (n + k)) d
  have hsum : (∑ k ∈ Finset.range d, (f (n + k + d + 1) - f (n + k + d))) =
      f (n + 2 * d) - f (n + d) := by
    convert ha using 1
    · apply Finset.sum_congr rfl
      intro k _
      congr 2 <;> omega
    · congr 2
      omega
  have hsum' : (∑ k ∈ Finset.range d, (f (n + k + 1) - f (n + k))) =
      f (n + d) - f n := by
    simpa only [Nat.add_zero, Nat.add_assoc] using hb
  rw [hsum, hsum']
  ring

/-- Exact arbitrary-step factorial difference from ANISO Lemma 5.4,
indexed at the left endpoint `n` to avoid truncated subtraction. -/
theorem log_factorialProduct_step_second_difference (n d : ℕ) :
    Real.log (factorialProduct (n + 2 * d)) -
      2 * Real.log (factorialProduct (n + d)) + Real.log (factorialProduct n) =
      (∑ k ∈ Finset.range d, ∑ l ∈ Finset.range d,
        Real.log ((n + k + l : ℕ) + 1 : ℝ)) - (d : ℝ)^2 * Real.log 2 := by
  rw [second_difference_rectangle (fun m => Real.log (factorialProduct m)) n d]
  simp_rw [log_factorialProduct_second_difference, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
