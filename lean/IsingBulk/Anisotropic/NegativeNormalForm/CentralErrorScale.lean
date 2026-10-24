import IsingBulk.Anisotropic.NegativeNormalForm.BetaDensityDimension

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section

/-- The removed model tail is smaller than the displayed density tail at every
Taylor order, so a single common relative-error scale controls both. -/
theorem half_pow_le_density_tail (j : ℕ) :
    (1/2:ℝ)^j≤Real.exp (-(j:ℝ)*Real.log 2/8) := by
  have he : (1/2:ℝ)^j=Real.exp (-(j:ℝ)*Real.log 2) := by
    rw [show -(j:ℝ)*Real.log 2=(j:ℝ)*(-Real.log 2) by ring,
      Real.exp_nat_mul,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [he]
  apply Real.exp_le_exp.mpr
  have hj : 0≤(j:ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  linarith

/-- Combining the density and cutoff errors preserves the exact scale already
controlled uniformly throughout the middle range. -/
theorem central_errors_le_density_scale (A Ct : ℝ) (hCt : 0≤Ct) (N j : ℕ) :
    A*((N:ℝ)/Real.sqrt j+(N:ℝ)^2/j+Real.exp (-(j:ℝ)*Real.log 2/8))+
      Ct*(1/2:ℝ)^j≤
    (A+Ct)*((N:ℝ)/Real.sqrt j+(N:ℝ)^2/j+Real.exp (-(j:ℝ)*Real.log 2/8)) := by
  have hh := mul_le_mul_of_nonneg_left (half_pow_le_density_tail j) hCt
  have hp : 0≤(N:ℝ)/Real.sqrt j+(N:ℝ)^2/j := by positivity
  nlinarith

end
end IsingBulk.Anisotropic.NegativeNormalForm
