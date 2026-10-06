import IsingBulk.Analysis.BranchLength
import Mathlib.MeasureTheory.Integral.Pi

/-! The separated branch majorant integrates with C^N cost. It contains
no occupancy variable, so Fubini does not hold a coupled occupancy fixed. -/
namespace IsingBulk.Tail
noncomputable section
open MeasureTheory Set
open scoped BigOperators

def branchMajorant (C ε u : ℝ) : ℝ := C/Real.sqrt (|u|+ε)

theorem branchMajorant_integral (C ε h : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) (hh : 0 ≤ h) :
    (∫ u in Icc (-h) h, branchMajorant C ε u) ≤ 4*C*Real.sqrt h := by
  have hi := IsingBulk.Branch.reciprocal_sqrt_integral ε h C hε hh hC
  rw [intervalIntegral.integral_of_le (by linarith : -h ≤ h),← integral_Icc_eq_integral_Ioc] at hi
  exact hi

theorem product_branchMajorant_integral (N : ℕ) (C ε h : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) (hh : 0 ≤ h) :
    (∫ u : Fin N → ℝ, ∏ i, branchMajorant C ε (u i)
      ∂Measure.pi (fun _ : Fin N => volume.restrict (Icc (-h) h))) ≤
      (4*C*Real.sqrt h)^N := by
  rw [integral_fintype_prod_eq_pow,Fintype.card_fin]
  apply pow_le_pow_left₀
  · exact integral_nonneg (fun u => by unfold branchMajorant; positivity)
  · exact branchMajorant_integral C ε h hC hε hh

end
end IsingBulk.Tail
