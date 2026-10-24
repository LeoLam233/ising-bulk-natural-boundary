import IsingBulk.Anisotropic.NegativeDominance.MiddleDensityScale

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

/-- The combined relative error from the actual central density and the
noncentral resonant windings throughout the middle particle range. -/
def actualMiddleErrorScale (E : ℝ) (j : ℕ) : ℝ :=
  E*middleDensityScale j+Real.exp (-(j:ℝ)*Real.log 2/4)

theorem actualMiddleErrorScale_nonneg {E : ℝ} (hE : 0≤E) (j : ℕ) :
    0≤actualMiddleErrorScale E j := by
  unfold actualMiddleErrorScale middleDensityScale
  positivity

theorem actualMiddleErrorScale_tendsto_zero (E : ℝ) :
    Tendsto (actualMiddleErrorScale E) atTop (𝓝 0) := by
  have hc : -(Real.log 2/4)<0 := by
    nlinarith [Real.log_pos (by norm_num : (1:ℝ)<2)]
  have ha := (tendsto_const_mul_atBot_of_neg hc).mpr tendsto_natCast_atTop_atTop
  have he := Real.tendsto_exp_atBot.comp ha
  have hh := (middleDensityScale_tendsto_zero.const_mul E).add he
  simp only [mul_zero,zero_add] at hh
  convert hh using 1
  funext j
  simp only [actualMiddleErrorScale,Function.comp_def]
  congr 2
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
