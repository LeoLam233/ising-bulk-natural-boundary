import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

/- INTENTIONALLY INVALID. Excluded from production imports and declaration counts. -/
-- EXPECT_FAILURE_DECLARATION: the complex sum vanishes, but the norm sum is two.
example : ‖(1 : ℂ) + (-1)‖ = ‖(1 : ℂ)‖ + ‖(-1 : ℂ)‖ := by
  -- EXPECT_FAILURE_HERE: cancellation cannot be used inside an absolute sum.
  norm_num
