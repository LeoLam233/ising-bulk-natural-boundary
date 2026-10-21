import IsingBulk.First.FirstCoefficient

/-! Geometry-only regular chart data, retaining the original acute data
and all old declarations unchanged. No analytic conclusion is stored. -/
namespace IsingBulk.First
noncomputable section

structure RegularChartData where
  alpha : ℝ
  beta : ℝ
  theta : ℝ
  alpha_pos : 0 < alpha
  alpha_lt_pi : alpha < Real.pi
  beta_pos : 0 < beta
  beta_lt_pi : beta < Real.pi
  theta_pos : 0 < theta
  theta_lt_pi : theta < Real.pi
  angle_relation : Real.cos alpha+Real.cos beta=2*Real.cos theta
  level_ne_zero : Real.cos alpha+Real.cos beta ≠ 0

namespace RegularChartData

def b (a : RegularChartData) : ℝ := Real.sin a.alpha/Real.sin a.beta

def d (a : RegularChartData) : ℝ :=
  (Real.cos a.alpha+Real.cos a.beta)*(1-Real.cos a.alpha*Real.cos a.beta)/
    (2*Real.sin a.beta^3)

def A₀ (a : RegularChartData) (c₀ : ℝ) : ℝ :=
  (2*Real.sin a.theta-c₀*Real.sin a.alpha)/Real.sin a.beta

def Q (a : RegularChartData) (N : ℕ) : ℝ := 2*N*Real.sin a.theta/Real.sin a.beta

def K (a : RegularChartData) (N : ℕ) : ℝ :=
  (2/(N.factorial:ℝ))*(2^(N*(N-1)))⁻¹*((2*Real.pi)^N)⁻¹*((Real.sin a.beta)^(N^2))⁻¹

def Ds (a : RegularChartData) (N : ℕ) : ℂ :=
  2*(N:ℂ)*Complex.exp (-Complex.I*a.theta)*(Real.sin a.theta:ℂ)/(Real.sin a.beta:ℂ)

theorem sin_alpha_pos (a : RegularChartData) : 0 < Real.sin a.alpha :=
  Real.sin_pos_of_pos_of_lt_pi a.alpha_pos a.alpha_lt_pi

theorem sin_beta_pos (a : RegularChartData) : 0 < Real.sin a.beta :=
  Real.sin_pos_of_pos_of_lt_pi a.beta_pos a.beta_lt_pi

theorem sin_theta_pos (a : RegularChartData) : 0 < Real.sin a.theta :=
  Real.sin_pos_of_pos_of_lt_pi a.theta_pos a.theta_lt_pi

theorem cosine_product_lt_one (a : RegularChartData) :
    Real.cos a.alpha*Real.cos a.beta < 1 := by
  have ha := Real.sin_sq_add_cos_sq a.alpha
  have hb := Real.sin_sq_add_cos_sq a.beta
  have hp := sq_pos_of_pos a.sin_alpha_pos
  nlinarith [sq_nonneg (Real.sin a.beta),sq_nonneg (Real.cos a.alpha-Real.cos a.beta)]

theorem b_pos (a : RegularChartData) : 0<a.b := div_pos a.sin_alpha_pos a.sin_beta_pos

theorem d_ne_zero (a : RegularChartData) : a.d ≠ 0 := by
  unfold d
  exact div_ne_zero (mul_ne_zero a.level_ne_zero (sub_pos.mpr a.cosine_product_lt_one).ne')
    (mul_ne_zero (by norm_num) (pow_ne_zero _ a.sin_beta_pos.ne'))

theorem Q_pos (a : RegularChartData) {N : ℕ} (hN : 0<N) : 0<a.Q N := by
  unfold Q
  exact div_pos (mul_pos (mul_pos (by norm_num) (by exact_mod_cast hN)) a.sin_theta_pos) a.sin_beta_pos

theorem K_pos (a : RegularChartData) (N : ℕ) : 0<a.K N := by
  have hs := a.sin_beta_pos
  unfold K
  positivity

theorem Ds_ne_zero (a : RegularChartData) {N : ℕ} (hN : 0<N) : a.Ds N ≠ 0 := by
  unfold Ds
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast hN.ne'))
      (Complex.exp_ne_zero _)) (Complex.ofReal_ne_zero.mpr a.sin_theta_pos.ne'))
    (Complex.ofReal_ne_zero.mpr a.sin_beta_pos.ne')

/-- Curvature sign, defined from the proved nonzero literal curvature. -/
def curvatureSign (a : RegularChartData) : ℝ := if 0<a.d then 1 else -1

theorem curvatureSign_cases (a : RegularChartData) : a.curvatureSign=1 ∨ a.curvatureSign= -1 := by
  unfold curvatureSign
  split_ifs <;> simp

theorem curvatureSign_mul_d (a : RegularChartData) : a.curvatureSign*a.d=|a.d| := by
  unfold curvatureSign
  split_ifs with hd
  · simp [abs_of_pos hd]
  · have hd' : a.d<0 := lt_of_le_of_ne (le_of_not_gt hd) a.d_ne_zero
    simp [abs_of_neg hd']

theorem physical_damping (a : RegularChartData) (c₀ : ℝ) :
    a.A₀ c₀+a.b*c₀=2*Real.sin a.theta/Real.sin a.beta := by
  unfold A₀ b
  ring

theorem curvature_identity (a : RegularChartData) :
    -(Real.cos a.alpha+Real.cos a.beta*a.b^2)/Real.sin a.beta= -2*a.d := by
  have hs := a.sin_beta_pos.ne'
  have ha := Real.sin_sq_add_cos_sq a.alpha
  have hb := Real.sin_sq_add_cos_sq a.beta
  unfold b d
  field_simp
  linear_combination -(Real.cos a.beta)*ha-(Real.cos a.alpha)*hb

def swap (a : RegularChartData) : RegularChartData where
  alpha := a.beta
  beta := a.alpha
  theta := a.theta
  alpha_pos := a.beta_pos
  alpha_lt_pi := a.beta_lt_pi
  beta_pos := a.alpha_pos
  beta_lt_pi := a.alpha_lt_pi
  theta_pos := a.theta_pos
  theta_lt_pi := a.theta_lt_pi
  angle_relation := by simpa only [add_comm] using a.angle_relation
  level_ne_zero := by simpa only [add_comm] using a.level_ne_zero

end RegularChartData

/-- Backward-compatible geometry map; all old acute fields remain unchanged. -/
def OrderedChartData.toRegular (a : OrderedChartData) : RegularChartData where
  alpha := a.alpha
  beta := a.beta
  theta := a.theta
  alpha_pos := a.alpha_pos
  alpha_lt_pi := by linarith [a.alpha_lt,Real.pi_pos]
  beta_pos := a.beta_pos
  beta_lt_pi := by linarith [a.beta_lt,Real.pi_pos]
  theta_pos := a.theta_pos
  theta_lt_pi := by linarith [a.theta_lt,Real.pi_pos]
  angle_relation := a.angle_relation
  level_ne_zero := (add_pos a.cos_alpha_pos a.cos_beta_pos).ne'

@[simp] theorem OrderedChartData.toRegular_b (a : OrderedChartData) : (a.toRegular).b=a.b := rfl
@[simp] theorem OrderedChartData.toRegular_d (a : OrderedChartData) : (a.toRegular).d=a.d := rfl
@[simp] theorem OrderedChartData.toRegular_Q (a : OrderedChartData) (N : ℕ) : (a.toRegular).Q N=a.Q N := rfl
@[simp] theorem OrderedChartData.toRegular_K (a : OrderedChartData) (N : ℕ) : (a.toRegular).K N=a.K N := rfl
@[simp] theorem OrderedChartData.toRegular_Ds (a : OrderedChartData) (N : ℕ) : (a.toRegular).Ds N=a.Ds N := rfl


end
end IsingBulk.First
