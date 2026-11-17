import IsingBulk.AnisoF002.C03.NegativeGaussianMarginalBound

/-!
# Exact neighboring constrained Gaussian normalization ratio

This is the ratio occurring in F002's actual one-coordinate marginal.
Both normalizing constants are the previously integrated independent-
coordinate Gaussian Vandermonde densities.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem constrainedMehtaProduct_succ (d : ℕ) :
    constrainedMehtaProduct (d + 1) = constrainedMehtaProduct d *
      ((d + 1).factorial : ℝ) / (2 : ℝ) ^ (d + 1) := by
  unfold constrainedMehtaProduct
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  ring

/-- The normalization ratio in the frozen one-coordinate marginal formula. -/
theorem constrained_gaussian_marginal_ratio (d : ℕ) :
    constrainedGaussianIntegral d / constrainedGaussianIntegral (d + 1) =
      (2 : ℝ) ^ (d + 1) / (Real.sqrt Real.pi * ((d + 2).factorial : ℝ)) *
        Real.sqrt (((d + 2 : ℕ) : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
  rw [constrained_gaussian_mehta, constrained_gaussian_mehta,
    constrainedMehtaProduct_succ, pow_succ, Real.sqrt_div (by positivity)]
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hn : Real.sqrt ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hn' : Real.sqrt ((d + 1 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : ((d + 1).factorial : ℝ) ≠ 0 := by positivity
  have hf' : ((d + 2).factorial : ℝ) ≠ 0 := by positivity
  have hP : constrainedMehtaProduct d ≠ 0 := (constrainedMehtaProduct_pos d).ne'
  have htwo : (2 : ℝ) ^ (d + 1) ≠ 0 := by positivity
  have hpp : (Real.sqrt Real.pi) ^ d ≠ 0 := pow_ne_zero _ hp
  have heq : d + 1 + 1 = d + 2 := by omega
  rw [heq]
  field_simp

theorem marginalScale_one_le (d : ℕ) : 1 ≤ marginalScale d := by
  rw [marginalScale_identity]
  have h : (0 : ℝ) ≤ (((d + 1 : ℕ) : ℝ))⁻¹ := by positivity
  linarith

end
end IsingBulk.AnisoF002.NegativeHT.Angular
