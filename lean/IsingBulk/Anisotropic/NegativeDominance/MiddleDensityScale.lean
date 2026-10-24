import IsingBulk.Anisotropic.NegativeDominance.HigherWindingMiddle

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

def middleDensityScale (j : ℕ) : ℝ :=
  1/Real.sqrt (Real.sqrt (Real.log (j : ℝ)))+1/Real.sqrt (Real.log (j : ℝ))+
    Real.exp (-(j : ℝ)*Real.log 2/8)

/-- Uniform relative-density error scale across the full middle range. -/
theorem density_scale_le_middle {N j : ℕ} (hj : 1<j)
    (hcut : (N : ℝ)^2≤(j : ℝ)/Real.sqrt (Real.log j)) :
    (N : ℝ)/Real.sqrt j+(N : ℝ)^2/j+Real.exp (-(j : ℝ)*Real.log 2/8)≤middleDensityScale j := by
  have hjp : (0 : ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have hlog : 0<Real.log (j : ℝ) := Real.log_pos (by exact_mod_cast hj)
  have hs : 0<Real.sqrt (Real.log (j : ℝ)) := Real.sqrt_pos.mpr hlog
  have hfrac : (N : ℝ)^2/j≤1/Real.sqrt (Real.log (j : ℝ)) := by
    apply (div_le_iff₀ hjp).mpr
    simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using hcut
  have hroot := Real.sqrt_le_sqrt hfrac
  rw [Real.sqrt_div (sq_nonneg (N : ℝ)),Real.sqrt_sq_eq_abs,abs_of_nonneg (Nat.cast_nonneg N),Real.sqrt_div (by norm_num : (0 : ℝ)≤1),Real.sqrt_one] at hroot
  dsimp [middleDensityScale]
  linarith only [hroot,hfrac]

theorem middleDensityScale_tendsto_zero : Tendsto middleDensityScale atTop (𝓝 0) := by
  have hl : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs := Real.tendsto_sqrt_atTop.comp hl
  have hss := Real.tendsto_sqrt_atTop.comp hs
  have hc : -(Real.log 2/8)<0 := by nlinarith [Real.log_pos (by norm_num : (1 : ℝ)<2)]
  have ha := (tendsto_const_mul_atBot_of_neg hc).mpr tendsto_natCast_atTop_atTop
  have he := Real.tendsto_exp_atBot.comp ha
  have hh := ((tendsto_inv_atTop_zero.comp hss).add (tendsto_inv_atTop_zero.comp hs)).add he
  simp only [Function.comp_def,zero_add] at hh
  convert hh using 1
  funext j
  simp only [middleDensityScale,one_div]
  congr 2
  ring

theorem eventually_middle_density_small {A ε : ℝ} (hA : 0≤A) (hε : 0<ε) :
    ∀ᶠ j : ℕ in atTop,∀N : ℕ,
      (N : ℝ)^2≤(j : ℝ)/Real.sqrt (Real.log j) →
      8*N^2≤j ∧ A*((N : ℝ)/Real.sqrt j+(N : ℝ)^2/j+Real.exp (-(j : ℝ)*Real.log 2/8))<ε := by
  have hs := Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun j => A*middleDensityScale j) atTop (𝓝 0) := by
    simpa only [mul_zero] using middleDensityScale_tendsto_zero.const_mul A
  filter_upwards [eventually_ge_atTop 2,hs.eventually_ge_atTop 8,hlim.eventually_lt_const hε] with j hj hs8 he
  intro N hcut
  dsimp only [Function.comp_def] at hs8
  have hSp : 0<Real.sqrt (Real.log (j : ℝ)) := by linarith
  have hcut' := (le_div_iff₀ hSp).mp hcut
  have hh := mul_le_mul_of_nonneg_left hs8 (sq_nonneg (N : ℝ))
  refine ⟨?_,(mul_le_mul_of_nonneg_left (density_scale_le_middle (by omega) hcut) hA).trans_lt he⟩
  exact_mod_cast (show (8 : ℝ)*(N : ℝ)^2≤j by nlinarith only [hcut',hh])

end
end IsingBulk.Anisotropic.NegativeDominance
