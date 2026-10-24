import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! Exact cumulative-sum identities for the growing integer Gamma shift.
These retain the unequal adjacent increments of α_n. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

def cumulative (f : ℕ → ℝ) (a : ℕ) : ℝ := ∑ m ∈ Finset.range a, f m

theorem cumulative_add (f : ℕ → ℝ) (a b : ℕ) :
    cumulative f (a + b) = cumulative f a + ∑ k ∈ Finset.range b, f (a + k) := by
  simp only [cumulative, Finset.sum_range_add]

/-- The unequal adjacent increments of α are retained exactly: the two
paired blocks have length `b`, and the excess block has length `d`. -/
theorem cumulative_second_difference (f : ℕ → ℝ) (a b d : ℕ) :
    cumulative f (a + 2 * b + d) - 2 * cumulative f (a + b) + cumulative f a =
      (∑ k ∈ Finset.range b, (f (a + b + k) - f (a + k))) +
        ∑ k ∈ Finset.range d, f (a + 2 * b + k) := by
  have hindex : a + 2 * b = (a + b) + b := by omega
  rw [cumulative_add f (a + 2 * b) d, hindex, cumulative_add f (a + b) b,
    cumulative_add f a b, Finset.sum_sub_distrib]
  ring

/-- A local Lipschitz estimate on the summands controls the entire exact
second difference, including its excess summands. -/
theorem cumulative_second_difference_le (f : ℕ → ℝ) (a b d : ℕ) (L U : ℝ)
    (hp : ∀ k, k < b → f (a + b + k) - f (a + k) ≤ b * L)
    (he : ∀ k, k < d → f (a + 2 * b + k) ≤ U) :
    cumulative f (a + 2 * b + d) - 2 * cumulative f (a + b) + cumulative f a ≤
      (b : ℝ)^2 * L + d * U := by
  rw [cumulative_second_difference]
  calc
    _ ≤ (∑ _k ∈ Finset.range b, (b : ℝ) * L) +
        ∑ _k ∈ Finset.range d, U := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun k hk => hp k (Finset.mem_range.mp hk))
      · exact Finset.sum_le_sum (fun k hk => he k (Finset.mem_range.mp hk))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end
end IsingBulk.Anisotropic.NegativeDominance
