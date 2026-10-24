import IsingBulk.Anisotropic.NegativeNormalForm.ActualDensityBeta

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open IsingBulk.Anisotropic.NegativeDominance

theorem betaDensityError_dimension (n j : ℕ) (hn : 3≤n) (hj : 8*n^2≤j)
    (C : ℝ) (hC : 0≤C) :
    betaDensityErrorBound n j (j/4) C≤
      expErrorConstant C 1*((n:ℝ)/Real.sqrt j+(n:ℝ)^2/j)+
        Real.exp (-(j:ℝ)*Real.log 2/8) := by
  have ha := (alpha_pos_and_twice_le n hn).2
  have haj : 2*alpha n≤j := by nlinarith
  have hlog : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  have hlogpos : 0<Real.log 2 := Real.log_pos (by norm_num)
  have har : 2*(alpha n:ℝ)≤(n:ℝ)^2 := by
    exact_mod_cast (show 2*alpha n≤n^2 by nlinarith)
  have hjr : 8*(n:ℝ)^2≤j := by exact_mod_cast hj
  have hentropy : (alpha n:ℝ)*Real.log 4≤(j:ℝ)*Real.log (1+1)/8 := by
    rw [hlog]
    norm_num only [show (1:ℝ)+1=2 by norm_num]
    have hh := mul_le_mul_of_nonneg_right har hlogpos.le
    have hh' := mul_le_mul_of_nonneg_right hjr hlogpos.le
    nlinarith
  have htail := beta_tail_factor_exponential (alpha n) j 1 (by norm_num) hentropy
  unfold betaDensityErrorBound
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left
      (add_le_add (beta_sqrt_moment_dimension_bound n j hn haj) (beta_moment_dimension_bound n j hn haj))
    unfold expErrorConstant
    positivity
  · simpa only [show (1:ℝ)+1=2 by norm_num] using htail

end
end IsingBulk.Anisotropic.NegativeNormalForm
