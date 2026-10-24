import IsingBulk.Anisotropic.NegativeDominance.ExactModel

/-! Exact particle arithmetic for the growing integer beta exponent. -/
namespace IsingBulk.Anisotropic.NegativeDominance

 theorem alpha_two_mul_add_one (k : ℕ) : alpha (2 * k + 1) = 2 * k * (k + 1) := by
  unfold alpha
  rw [show (2 * k + 1) * (2 * k + 1) = 2 * (2 * k * (k + 1)) + 1 by ring]
  omega

/-- Odd particle dimensions give exactly the integer exponent stated in
the manuscript, not a rounded approximation. -/
theorem two_mul_alpha_add_one (n : ℕ) (hn : Odd n) : 2 * alpha n + 1 = n * n := by
  obtain ⟨k, rfl⟩ := hn
  rw [alpha_two_mul_add_one]
  ring

/-- Exact increment of α along an even particle step. -/
theorem alpha_even_step (n p : ℕ) (hn : Odd n) :
    alpha (n + 2 * p) = alpha n + 2 * p * n + 2 * p^2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [show 2 * k + 1 + 2 * p = 2 * (k + p) + 1 by ring,
    alpha_two_mul_add_one, alpha_two_mul_add_one]
  ring

/-- The upper alpha increment exceeds the lower by the square of the
particle step, exactly as required in the Gamma second difference. -/
theorem alpha_even_step_second_difference (n p : ℕ) (hn : Odd n) :
    alpha (n + 4 * p) + alpha n = 2 * alpha (n + 2 * p) + (2 * p)^2 := by
  rw [show n + 4 * p = n + 2 * (2 * p) by ring,
    alpha_even_step n (2 * p) hn, alpha_even_step n p hn]
  ring

end IsingBulk.Anisotropic.NegativeDominance
