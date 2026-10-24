import IsingBulk.Anisotropic.Final.ContinuousRootUniqueness
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace IsingBulk.Anisotropic
noncomputable section

def positiveFourthRoot (t : ℝ) : ℝ := Real.sqrt (Real.sqrt t)

theorem positiveFourthRoot_pos {t : ℝ} (ht : 0<t) : 0<positiveFourthRoot t :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr ht)

theorem positiveFourthRoot_pow_four {t : ℝ} (ht : 0≤t) : positiveFourthRoot t^4=t := by
  unfold positiveFourthRoot
  rw [show 4=2*2 from rfl,pow_mul,Real.sq_sqrt (Real.sqrt_nonneg t),Real.sq_sqrt ht]

theorem positiveFourthRoot_continuous : Continuous positiveFourthRoot :=
  Real.continuous_sqrt.comp Real.continuous_sqrt

end
end IsingBulk.Anisotropic
