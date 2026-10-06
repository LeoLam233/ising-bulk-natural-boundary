import IsingBulk.First.SwappedPeriodScaling

/-! The two actual ordered charts have equal leading coefficients, including
phase. The proof uses a positive real change of variables in the actual period. -/
namespace IsingBulk.First
noncomputable section
open Complex

namespace OrderedChartData

def swap (a : OrderedChartData) : OrderedChartData where
  alpha := a.beta
  beta := a.alpha
  theta := a.theta
  alpha_pos := a.beta_pos
  alpha_lt := a.beta_lt
  beta_pos := a.alpha_pos
  beta_lt := a.alpha_lt
  theta_pos := a.theta_pos
  theta_lt := a.theta_lt
  angle_relation := by simpa only [add_comm] using a.angle_relation

def swapRatio (a : OrderedChartData) : ℝ := Real.sin a.beta / Real.sin a.alpha

theorem swapRatio_pos (a : OrderedChartData) : 0 < a.swapRatio :=
  div_pos a.sin_beta_pos a.sin_alpha_pos

theorem swap_Q (a : OrderedChartData) (N : ℕ) : a.swap.Q N = a.swapRatio*a.Q N := by
  dsimp [Q,swap,swapRatio]
  field_simp [a.sin_alpha_pos.ne', a.sin_beta_pos.ne']

theorem swap_d (a : OrderedChartData) : a.swap.d = a.swapRatio^3*a.d := by
  dsimp [d,swap,swapRatio]
  field_simp [a.sin_alpha_pos.ne', a.sin_beta_pos.ne']
  ring

theorem swap_Ds (a : OrderedChartData) (N : ℕ) : a.swap.Ds N = (a.swapRatio:ℂ)*a.Ds N := by
  dsimp [Ds,swap,swapRatio]
  simp only [ofReal_div]
  field_simp [ofReal_ne_zero.mpr a.sin_alpha_pos.ne', ofReal_ne_zero.mpr a.sin_beta_pos.ne']
  norm_cast
  field_simp [a.sin_alpha_pos.ne', a.sin_beta_pos.ne']

theorem swap_K (a : OrderedChartData) (N : ℕ) : a.swap.K N = a.swapRatio^(N^2)*a.K N := by
  dsimp [K,swap,swapRatio]
  rw [div_pow]
  field_simp [a.sin_alpha_pos.ne', a.sin_beta_pos.ne']

end OrderedChartData

theorem localLeadingCoefficient_swap (a : OrderedChartData) (n k : ℕ) :
    localLeadingCoefficient a.swap n k = localLeadingCoefficient a n k := by
  have hJ := shapePeriod_weighted_scaling n k (a.Q (n+1)) (-I*a.d) a.swapRatio_pos
  have hd : -I*(a.swap.d:ℂ) = (a.swapRatio:ℂ)^3*(-I*a.d) := by
    rw [a.swap_d]
    push_cast
    ring
  unfold localLeadingCoefficient
  rw [a.swap_K, a.swap_Ds, a.swap_Q, hd]
  simp only [ofReal_mul, ofReal_pow, ofReal_ofNat, mul_pow]
  linear_combination (2:ℂ)*(Real.pi:ℂ) * (a.K (n+1):ℂ) * (-1:ℂ)^k *
    (k.factorial:ℂ) * a.Ds (n+1)^k * hJ

theorem two_ordered_leading_coefficients (a : OrderedChartData) {n : ℕ}
    (hn : 1 ≤ n) (he : Even (n+1)) :
    localLeadingCoefficient a n ((n+1)^2/2-1) +
      localLeadingCoefficient a.swap n ((n+1)^2/2-1) =
        2*localLeadingCoefficient a n ((n+1)^2/2-1) ∧
    localLeadingCoefficient a n ((n+1)^2/2-1) +
      localLeadingCoefficient a.swap n ((n+1)^2/2-1) ≠ 0 := by
  rw [localLeadingCoefficient_swap]
  constructor
  · ring
  · rw [← two_mul]
    exact mul_ne_zero (by norm_num) (localLeadingCoefficient_ne_zero a hn he)

end
end IsingBulk.First
