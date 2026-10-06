import IsingBulk.First.ShapeSource
import IsingBulk.First.MeanPhase

/-! Literal FIRST coefficient formulas and their elementary factor properties.
Identification with the differentiated physical density is a separate obligation. -/
namespace IsingBulk.First
noncomputable section

namespace OrderedChartData

/-- The displayed normalized local coefficient, with negative integer powers
written as reciprocals of natural powers. -/
def K (a : OrderedChartData) (N : ℕ) : ℝ :=
  (2 / (N.factorial : ℝ)) * (2 ^ (N*(N-1)))⁻¹ *
    ((2*Real.pi)^N)⁻¹ * ((Real.sin a.beta)^(N^2))⁻¹

def Ds (a : OrderedChartData) (N : ℕ) : ℂ :=
  2 * (N : ℂ) * Complex.exp (-Complex.I * a.theta) *
    (Real.sin a.theta : ℂ) / (Real.sin a.beta : ℂ)

theorem K_pos (a : OrderedChartData) (N : ℕ) : 0 < a.K N := by
  have hs := a.sin_beta_pos
  unfold K
  positivity

theorem Ds_ne_zero (a : OrderedChartData) {N : ℕ} (hN : 0 < N) : a.Ds N ≠ 0 := by
  unfold Ds
  apply div_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (by exact_mod_cast hN.ne')
      · exact Complex.exp_ne_zero _
    · exact Complex.ofReal_ne_zero.mpr a.sin_theta_pos.ne'
  · exact Complex.ofReal_ne_zero.mpr a.sin_beta_pos.ne'

end OrderedChartData

/-- The displayed leading local coefficient uses the actual constrained period. -/
def localLeadingCoefficient (a : OrderedChartData) (n k : ℕ) : ℂ :=
  (2*Real.pi : ℝ) * (a.K (n+1) : ℂ) * (-1 : ℂ)^k * (k.factorial : ℂ) *
    a.Ds (n+1)^k * shapePeriod n k (a.Q (n+1)) (-Complex.I*a.d)

/-- Factor algebra only. The period premise is discharged by the independently
proved shape-period theorem when forming the source-facing endpoint. -/
theorem localLeadingCoefficient_ne_zero_of_period (a : OrderedChartData) (n k : ℕ)
    (hJ : shapePeriod n k (a.Q (n+1)) (-Complex.I*a.d) ≠ 0) :
    localLeadingCoefficient a n k ≠ 0 := by
  unfold localLeadingCoefficient
  apply mul_ne_zero _ hJ
  apply mul_ne_zero _ (pow_ne_zero _ (a.Ds_ne_zero (by omega)))
  apply mul_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero k)
  apply mul_ne_zero _ (pow_ne_zero _ (by norm_num))
  exact mul_ne_zero (by exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))
    (Complex.ofReal_ne_zero.mpr (a.K_pos _).ne')

end
end IsingBulk.First
