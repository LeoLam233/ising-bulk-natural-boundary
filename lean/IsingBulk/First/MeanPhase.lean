import IsingBulk.Analysis.JetsChart
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Fixed ordered regular-chart data and the exact coefficients used by FIRST.
This module imports the audited scalar branch expressions without modifying them. -/
namespace IsingBulk.First
noncomputable section

/-- Preceding selected-angle data only: none of the mean-residue conclusions
is a field of this structure. Particle number and root-of-unity conditions are
supplied separately when the actual product pole is formed. -/
structure OrderedChartData where
  alpha : ℝ
  beta : ℝ
  theta : ℝ
  alpha_pos : 0 < alpha
  alpha_lt : alpha < Real.pi / 2
  beta_pos : 0 < beta
  beta_lt : beta < Real.pi / 2
  theta_pos : 0 < theta
  theta_lt : theta < Real.pi / 2
  angle_relation : Real.cos alpha + Real.cos beta = 2 * Real.cos theta

namespace OrderedChartData

def b (a : OrderedChartData) : ℝ := Real.sin a.alpha / Real.sin a.beta

def d (a : OrderedChartData) : ℝ :=
  (Real.cos a.alpha + Real.cos a.beta) * (1 - Real.cos a.alpha * Real.cos a.beta) /
    (2 * Real.sin a.beta ^ 3)

def A₀ (a : OrderedChartData) (c₀ : ℝ) : ℝ :=
  (2 * Real.sin a.theta - c₀ * Real.sin a.alpha) / Real.sin a.beta

def Q (a : OrderedChartData) (N : ℕ) : ℝ :=
  2 * N * Real.sin a.theta / Real.sin a.beta

theorem sin_alpha_pos (a : OrderedChartData) : 0 < Real.sin a.alpha :=
  Real.sin_pos_of_pos_of_lt_pi a.alpha_pos (by linarith [a.alpha_lt, Real.pi_pos])

theorem sin_beta_pos (a : OrderedChartData) : 0 < Real.sin a.beta :=
  Real.sin_pos_of_pos_of_lt_pi a.beta_pos (by linarith [a.beta_lt, Real.pi_pos])

theorem sin_theta_pos (a : OrderedChartData) : 0 < Real.sin a.theta :=
  Real.sin_pos_of_pos_of_lt_pi a.theta_pos (by linarith [a.theta_lt, Real.pi_pos])

theorem cos_alpha_pos (a : OrderedChartData) : 0 < Real.cos a.alpha :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [a.alpha_pos, Real.pi_pos], a.alpha_lt⟩

theorem cos_beta_pos (a : OrderedChartData) : 0 < Real.cos a.beta :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [a.beta_pos, Real.pi_pos], a.beta_lt⟩

theorem cosine_product_lt_one (a : OrderedChartData) :
    Real.cos a.alpha * Real.cos a.beta < 1 := by
  have hca := Real.cos_le_one a.alpha
  have hcb := Real.cos_le_one a.beta
  have hsa := a.sin_alpha_pos
  have hsq := Real.sin_sq_add_cos_sq a.alpha
  have hca' : Real.cos a.alpha < 1 := by nlinarith [sq_pos_of_pos hsa]
  have hprod := mul_le_mul_of_nonneg_left hcb a.cos_alpha_pos.le
  nlinarith

theorem b_pos (a : OrderedChartData) : 0 < a.b :=
  div_pos a.sin_alpha_pos a.sin_beta_pos

theorem d_pos (a : OrderedChartData) : 0 < a.d := by
  unfold d
  exact div_pos (mul_pos (add_pos a.cos_alpha_pos a.cos_beta_pos)
    (sub_pos.mpr a.cosine_product_lt_one))
    (mul_pos (by norm_num) (pow_pos a.sin_beta_pos 3))

theorem Q_pos (a : OrderedChartData) {N : ℕ} (hN : 0 < N) : 0 < a.Q N := by
  unfold Q
  exact div_pos (mul_pos (mul_pos (by norm_num) (by exact_mod_cast hN)) a.sin_theta_pos)
    a.sin_beta_pos

/-- The residue removes the radius-dependent part of the damping exactly. -/
theorem physical_damping (a : OrderedChartData) (c₀ : ℝ) :
    a.A₀ c₀ + a.b * c₀ = 2 * Real.sin a.theta / Real.sin a.beta := by
  unfold A₀ b
  ring

theorem physical_damping_N (a : OrderedChartData) (N : ℕ) (c₀ : ℝ) :
    N * (a.A₀ c₀ + a.b * c₀) = a.Q N := by
  rw [a.physical_damping]
  unfold Q
  ring

/-- Any independently obtained global residue threshold can be met at once
with the actual mean-chart attenuation requirement A₀>c₀. -/
theorem exists_admissible_c₀ (a : OrderedChartData) {c : ℝ} (hc : 0 < c) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ < c ∧ c₀ < a.A₀ c₀ := by
  let bound := 2 * Real.sin a.theta / (Real.sin a.alpha + Real.sin a.beta)
  have hb : 0 < bound := div_pos (mul_pos (by norm_num) a.sin_theta_pos)
    (add_pos a.sin_alpha_pos a.sin_beta_pos)
  refine ⟨min c bound / 2, half_pos (lt_min hc hb), ?_, ?_⟩
  · exact (half_lt_self (lt_min hc hb)).trans_le (min_le_left c bound)
  · have hlt : min c bound / 2 < bound :=
      (half_lt_self (lt_min hc hb)).trans_le (min_le_right c bound)
    have hmul := (lt_div_iff₀ (add_pos a.sin_alpha_pos a.sin_beta_pos)).mp hlt
    apply (lt_div_iff₀ a.sin_beta_pos).mpr
    nlinarith

/-- The second implicit angular derivative reduces to the source curvature. -/
theorem curvature_identity (a : OrderedChartData) :
    -(Real.cos a.alpha + Real.cos a.beta * a.b ^ 2) / Real.sin a.beta = -2 * a.d := by
  have hs : Real.sin a.beta ≠ 0 := ne_of_gt a.sin_beta_pos
  have ha := Real.sin_sq_add_cos_sq a.alpha
  have hb := Real.sin_sq_add_cos_sq a.beta
  unfold b d
  field_simp
  linear_combination -(Real.cos a.beta)*ha - (Real.cos a.alpha)*hb

end OrderedChartData
end
end IsingBulk.First
