import IsingBulk.Anisotropic.NegativeDominance.GammaDifferences
import IsingBulk.Anisotropic.NegativeDominance.OddIndices

/-! The exact Gamma correction estimate specialized to the growing ANISO
exponent α_n=(n²−1)/2 on the admissible odd-particle progression. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

theorem gammaCorrection_alpha_second_difference_bounds
    (n p : ℕ) (hn : Odd n) (j : ℝ) (hj : (alpha (n + 4 * p) : ℝ) < j) :
    let D := gammaCorrection (alpha (n + 4 * p)) j -
      2 * gammaCorrection (alpha (n + 2 * p)) j + gammaCorrection (alpha n) j
    0 ≤ D ∧ D ≤ (((2 * p * n + 2 * p^2 : ℕ) : ℝ)^2 +
      ((2 * p)^2 : ℕ) * (alpha (n + 4 * p) : ℝ)) / (j - alpha (n + 4 * p)) := by
  have hlow := alpha_even_step n p hn
  have hhigh : alpha (n + 4 * p) = alpha n +
      2 * (2 * p * n + 2 * p^2) + (2 * p)^2 := by
    rw [show n + 4 * p = n + 2 * (2 * p) by ring, alpha_even_step n (2 * p) hn]
    ring
  rw [hhigh] at hj
  simpa only [hlow, hhigh, Nat.add_assoc] using
    gammaCorrection_second_difference_bounds (alpha n) (2 * p * n + 2 * p^2) ((2 * p)^2) j hj

end
end IsingBulk.Anisotropic.NegativeDominance
