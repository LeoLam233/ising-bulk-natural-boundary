import IsingBulk.Anisotropic.NegativeDominance.ConstrainedBallMass

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

/-- Elementary entropy estimate for the actual constrained Vandermonde mass.
It has the precise negative N² log N order needed in the all-j high range. -/
theorem ball_mass_envelope_entropy (N : ℕ) (hN : 2≤N) :
    2^(N-1)*(16/(N : ℝ))^(N.choose 2) ≤
      Real.exp (-(N : ℝ)^2/2*Real.log N+10*(N : ℝ)^2) := by
  have hNR : (2 : ℝ)≤N := by exact_mod_cast hN
  have hNp : (0 : ℝ)<N := by linarith
  have hNm : ((N-1 : ℕ) : ℝ)=(N : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hc := Nat.cast_choose_two (K := ℝ) N
  have hc0 : (0 : ℝ)≤N.choose 2 := by positivity
  have hlogN : Real.log (N : ℝ)≤(N : ℝ)-1 := Real.log_le_sub_one_of_pos hNp
  have hlog2 : Real.log 2≤1 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2); linarith
  have hlog16 : Real.log 16≤15 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<16); linarith
  have hfirst : ((N-1 : ℕ) : ℝ)*Real.log 2≤(N : ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hlog2 (show (0 : ℝ)≤N-1 by linarith)
    rw [hNm]
    nlinarith only [hh,hNR]
  have hpairs : (N.choose 2 : ℝ)*Real.log 16≤15*(N : ℝ)^2/2 := by
    have hh := mul_le_mul_of_nonneg_left hlog16 hc0
    nlinarith only [hh,hc,hNR]
  have hcancel : -(N.choose 2 : ℝ)*Real.log N≤
      -(N : ℝ)^2/2*Real.log N+(N : ℝ)^2/2 := by
    have hh := mul_le_mul_of_nonneg_left hlogN hNp.le
    rw [hc]
    nlinarith only [hh,hNp.le]
  apply (Real.log_le_iff_le_exp (by positivity : 0<2^(N-1)*(16/(N : ℝ))^(N.choose 2))).mp
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,
    Real.log_div (by norm_num) hNp.ne']
  nlinarith only [hfirst,hpairs,hcancel,sq_nonneg (N : ℝ)]

/-- The literal ball integral has the required all-particle entropy scale. -/
theorem constrainedBallMass_entropy {n : ℕ} (hn : 1≤n) :
    constrainedBallMass n≤Real.exp (-((n+1 : ℕ) : ℝ)^2/2*Real.log (n+1)+10*((n+1 : ℕ) : ℝ)^2) := by
  have hh := ball_mass_envelope_entropy (n+1) (by omega)
  simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using (constrainedBallMass_bound hn).trans hh

end
end IsingBulk.Anisotropic.NegativeDominance
