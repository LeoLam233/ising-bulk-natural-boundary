import IsingBulk.First.RegularChartData
import IsingBulk.HT.First.OddShapePeriod

/-! The same actual constrained-period coefficient on both regular signs.
Its nonvanishing is proved from the radial primitive and angular positivity,
without a Gaussian-normalization premise. Source asymptotic attachment is separate. -/
namespace IsingBulk.HT.First.Regular
noncomputable section
open Complex IsingBulk.First

/-- The displayed leading local coefficient uses the actual constrained period. -/
def localLeadingCoefficient (a : IsingBulk.First.RegularChartData) (n k : ℕ) : ℂ :=
  (2*Real.pi : ℝ) * (a.K (n+1) : ℂ) * (-1 : ℂ)^k * (k.factorial : ℂ) *
    a.Ds (n+1)^k * shapePeriod n k (a.Q (n+1)) (-Complex.I*a.d)

/-- Factor algebra only. The period premise is discharged by the independently
proved shape-period theorem when forming the source-facing endpoint. -/
theorem localLeadingCoefficient_ne_zero_of_period (a : IsingBulk.First.RegularChartData) (n k : ℕ)
    (hJ : shapePeriod n k (a.Q (n+1)) (-Complex.I*a.d) ≠ 0) :
    localLeadingCoefficient a n k ≠ 0 := by
  unfold localLeadingCoefficient
  apply mul_ne_zero _ hJ
  apply mul_ne_zero _ (pow_ne_zero _ (a.Ds_ne_zero (by omega)))
  apply mul_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero k)
  apply mul_ne_zero _ (pow_ne_zero _ (by norm_num))
  exact mul_ne_zero (by exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))
    (Complex.ofReal_ne_zero.mpr (a.K_pos _).ne')


def swapRatio (a : IsingBulk.First.RegularChartData) : ℝ := Real.sin a.beta / Real.sin a.alpha

theorem swapRatio_pos (a : IsingBulk.First.RegularChartData) : 0 < (swapRatio a) :=
  div_pos a.sin_beta_pos a.sin_alpha_pos

theorem swap_Q (a : IsingBulk.First.RegularChartData) (N : ℕ) : a.swap.Q N = (swapRatio a)*a.Q N := by
  dsimp [IsingBulk.First.RegularChartData.Q,IsingBulk.First.RegularChartData.swap,swapRatio]
  field_simp [a.sin_alpha_pos.ne', a.sin_beta_pos.ne']

theorem swap_d (a : IsingBulk.First.RegularChartData) : a.swap.d = (swapRatio a)^3*a.d := by
  dsimp [IsingBulk.First.RegularChartData.d,IsingBulk.First.RegularChartData.swap,swapRatio]
  field_simp [a.sin_alpha_pos.ne', a.sin_beta_pos.ne']
  ring

theorem swap_Ds (a : IsingBulk.First.RegularChartData) (N : ℕ) : a.swap.Ds N = ((swapRatio a):ℂ)*a.Ds N := by
  dsimp [IsingBulk.First.RegularChartData.Ds,IsingBulk.First.RegularChartData.swap,swapRatio]
  simp only [ofReal_div]
  field_simp [ofReal_ne_zero.mpr a.sin_alpha_pos.ne', ofReal_ne_zero.mpr a.sin_beta_pos.ne']
  norm_cast
  field_simp [a.sin_alpha_pos.ne', a.sin_beta_pos.ne']

theorem swap_K (a : IsingBulk.First.RegularChartData) (N : ℕ) : a.swap.K N = (swapRatio a)^(N^2)*a.K N := by
  dsimp [IsingBulk.First.RegularChartData.K,IsingBulk.First.RegularChartData.swap,swapRatio]
  rw [div_pow]
  field_simp [a.sin_alpha_pos.ne', a.sin_beta_pos.ne']

theorem localLeadingCoefficient_swap (a : IsingBulk.First.RegularChartData) (n k : ℕ) :
    localLeadingCoefficient a.swap n k = localLeadingCoefficient a n k := by
  have hJ := shapePeriod_weighted_scaling n k (a.Q (n+1)) (-I*a.d) (swapRatio_pos a)
  have hd : -I*(a.swap.d:ℂ) = ((swapRatio a):ℂ)^3*(-I*a.d) := by
    rw [(swap_d a)]
    push_cast
    ring
  unfold localLeadingCoefficient
  rw [(swap_K a), (swap_Ds a), (swap_Q a), hd]
  simp only [ofReal_mul, ofReal_pow, ofReal_ofNat, mul_pow]
  linear_combination (2:ℂ)*(Real.pi:ℂ) * (a.K (n+1):ℂ) * (-1:ℂ)^k *
    (k.factorial:ℂ) * a.Ds (n+1)^k * hJ


/-- Genuine constrained-period coefficient for either curvature sign. -/
def oddLocalLeadingCoefficient (a : IsingBulk.First.RegularChartData) (p : ℕ) : ℂ :=
  -Complex.I*localLeadingCoefficient a (p-1) (derivativeOrder p)

theorem oddLocalLeadingCoefficient_ne_zero (a : IsingBulk.First.RegularChartData)
    {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) : oddLocalLeadingCoefficient a p ≠ 0 := by
  apply mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
  apply localLeadingCoefficient_ne_zero_of_period
  exact odd_shapePeriod_ne_zero hp hp3 (a.Q_pos (by omega)) a.d_ne_zero

theorem oddLocalLeadingCoefficient_swap (a : IsingBulk.First.RegularChartData) (p : ℕ) :
    oddLocalLeadingCoefficient a.swap p = oddLocalLeadingCoefficient a p := by
  unfold oddLocalLeadingCoefficient
  rw [localLeadingCoefficient_swap]

@[simp] theorem oddLocalLeadingCoefficient_toRegular (a : OrderedChartData) (p : ℕ) :
    oddLocalLeadingCoefficient a.toRegular p = IsingBulk.HT.First.oddLocalLeadingCoefficient a p := rfl

theorem four_oddLocalLeadingCoefficient_ne_zero (a : IsingBulk.First.RegularChartData)
    {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) : 4*oddLocalLeadingCoefficient a p ≠ 0 :=
  mul_ne_zero (by norm_num) (oddLocalLeadingCoefficient_ne_zero a hp hp3)

end
end IsingBulk.HT.First.Regular
