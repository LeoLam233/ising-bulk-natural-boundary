import IsingBulk.First.RegularChartData
import IsingBulk.HT22.First.RadialPeriod

/-! Literal equal-angle chart data on both upper quadrants. These carry only
geometric data; no singularity, tail or no-extension conclusion is a field. -/
namespace IsingBulk.HT22
noncomputable section
open IsingBulk.First IsingBulk.HT.First

def equalAngleRegularData (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi)
    (hc : Real.cos α≠0) : IsingBulk.First.RegularChartData where
  alpha := α
  beta := α
  theta := α
  alpha_pos := hα
  alpha_lt_pi := hαπ
  beta_pos := hα
  beta_lt_pi := hαπ
  theta_pos := hα
  theta_lt_pi := hαπ
  angle_relation := by ring
  level_ne_zero := by simpa only [← two_mul] using mul_ne_zero (by norm_num : (2:ℝ)≠0) hc

theorem equalAngleRegularData_d (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi)
    (hc : Real.cos α≠0) :
    (equalAngleRegularData α hα hαπ hc).d=Real.cos α/Real.sin α := by
  have hs : Real.sin α≠0 := (Real.sin_pos_of_pos_of_lt_pi hα hαπ).ne'
  dsimp [equalAngleRegularData,RegularChartData.d]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq α]

theorem equalAngleRegularData_Q (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi)
    (hc : Real.cos α≠0) (N : ℕ) :
    (equalAngleRegularData α hα hαπ hc).Q N=2*N := by
  have hs : Real.sin α≠0 := (Real.sin_pos_of_pos_of_lt_pi hα hαπ).ne'
  dsimp [equalAngleRegularData,RegularChartData.Q]
  field_simp

def equalAngleAmplitude (p : ℕ) (α : ℝ) : ℝ :=
  2/((p.factorial:ℝ)*(2*Real.pi)^(p-1)*2^(p*(p-1))*(Real.sin α)^(p^2))

theorem equalAngleAmplitude_pos (p : ℕ) {α : ℝ} (hα : 0<α) (hαπ : α<Real.pi) :
    0<equalAngleAmplitude p α := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hα hαπ
  unfold equalAngleAmplitude
  positivity

/-- The free-coordinate measure retains its 2pi conversion relative to
ambient post-mean data; no tangent/ambient Jacobian is interchanged. -/
theorem equalAngleAmplitude_eq_K {p : ℕ} (hp : 0<p)
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0) :
    equalAngleAmplitude p α = 2*Real.pi*(equalAngleRegularData α hα hαπ hc).K p := by
  have hp' : p=p-1+1 := by omega
  have hpow : (2*Real.pi)^p=(2*Real.pi)^(p-1)*(2*Real.pi) := by
    conv_lhs => rw [hp']
    rw [pow_succ]
  have hpi : 2*Real.pi≠0 := by positivity
  dsimp [equalAngleAmplitude,equalAngleRegularData,RegularChartData.K]
  rw [hpow]
  field_simp

/-- Exact two-reflected-chart coefficient; connection to the actual
localized integral is a separate source-identification theorem. -/
def equalAngleLeadingCoefficient (p : ℕ) (α : ℝ) : ℂ :=
  -2*Complex.I*(equalAngleAmplitude p α:ℂ)*((derivativeOrder p).factorial:ℂ)*
    (2*(p:ℂ))^(derivativeOrder p)*
    Complex.exp (-(α:ℂ)*Complex.I)^(derivativeOrder p)*
    shapePeriod (p-1) (derivativeOrder p) (2*p) (-Complex.I*(Real.cos α/Real.sin α))

theorem equalAngleLeadingCoefficient_ne_zero {p : ℕ} (hp : Odd p) (hp3 : 3≤p)
    {α : ℝ} (hα : 0<α) (hαπ : α<Real.pi) (hc : Real.cos α≠0) :
    equalAngleLeadingCoefficient p α≠0 := by
  have hs : Real.sin α≠0 := (Real.sin_pos_of_pos_of_lt_pi hα hαπ).ne'
  have hQ : (0:ℝ)<2*p := by positivity
  have hperiod := odd_shapePeriod_ne_zero hp hp3 hQ (div_ne_zero hc hs)
  simp only [Complex.ofReal_div] at hperiod
  unfold equalAngleLeadingCoefficient
  apply mul_ne_zero _ hperiod
  apply mul_ne_zero _ (pow_ne_zero _ (Complex.exp_ne_zero _))
  apply mul_ne_zero _ (pow_ne_zero _ (mul_ne_zero (by norm_num)
    (by exact_mod_cast (show p≠0 by omega))))
  apply mul_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero (derivativeOrder p))
  apply mul_ne_zero _ (Complex.ofReal_ne_zero.mpr (equalAngleAmplitude_pos p hα hαπ).ne')
  exact mul_ne_zero (by norm_num) Complex.I_ne_zero

end
end IsingBulk.HT22
