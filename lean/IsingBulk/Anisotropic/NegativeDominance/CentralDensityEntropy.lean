import IsingBulk.Anisotropic.NegativeDominance.BetaModelComparison
import IsingBulk.Anisotropic.NegativeDominance.EntropyFirstDifference

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

/-- Exact modulus logarithm of the actual full central residue. -/
theorem log_norm_centralDensity (Bn rootBn : ℂ) (s : ℝ) {N : ℕ}
    (hN : 0<N) (hB : Bn≠0) (hr : rootBn≠0) (hs : s≠0) :
    Real.log ‖centralDensity Bn rootBn s N‖=
      Real.log 2+(alpha N : ℝ)*Real.log ‖Bn‖-Real.log ‖rootBn‖-
        Real.log N-Real.log (N.factorial : ℝ)-((N-1 : ℕ) : ℝ)*Real.log (2*Real.pi)-
        (N*(N-1) : ℕ)*Real.log 2-(2*alpha N : ℕ)*Real.log |s| := by
  have hn : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
  have hf : (N.factorial : ℝ)≠0 := by positivity
  have hb := norm_ne_zero_iff.mpr hB
  have hr' := norm_ne_zero_iff.mpr hr
  have hs' : |s|≠0 := abs_ne_zero.mpr hs
  simp only [centralDensity,norm_div,norm_mul,norm_neg,norm_pow,Complex.norm_ofNat,
    Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  simp [Real.log_div,Real.log_mul,Real.log_pow,hn,hf,hb,hr',hs',Real.pi_ne_zero]
  ring

/-- Only quadratic entropy can be lost in the scalar central normalization. -/
theorem centralDensity_log_lower (Bn rootBn : ℂ) (s L : ℝ) {N : ℕ}
    (hN : 2≤N) (hB : Bn≠0) (hr : rootBn≠0) (hs : s≠0) (hL : 1≤L)
    (hbL : |Real.log ‖Bn‖|≤L) (hrL : |Real.log ‖rootBn‖|≤L)
    (hsL : |Real.log (|s|)|≤L) (hpL : Real.log (2*Real.pi)≤L) (h2L : Real.log 2≤L) :
    -10*(L+1)*(N : ℝ)^2≤Real.log ‖centralDensity Bn rootBn s N‖ := by
  have hNR : (2 : ℝ)≤N := by exact_mod_cast hN
  have hNp : (0 : ℝ)<N := by linarith
  have haN : alpha N≤N^2 := by
    simpa only [alpha,pow_two] using (Nat.div_le_self (N*N-1) 2).trans (Nat.sub_le (N*N) 1)
  have ha : (alpha N : ℝ)≤(N : ℝ)^2 := by exact_mod_cast haN
  have hnm : ((N-1 : ℕ) : ℝ)=(N : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hlogN : Real.log (N : ℝ)≤(N : ℝ)^2 := by
    have hh := Real.log_le_sub_one_of_pos hNp
    nlinarith only [hh,hNR]
  have hfac : Real.log (N.factorial : ℝ)≤(N : ℝ)^2 := by
    have hh := Real.log_le_log (show (0 : ℝ)<N.factorial by positivity)
      (show (N.factorial : ℝ)≤(N : ℝ)^N by exact_mod_cast Nat.factorial_le_pow N)
    rw [Real.log_pow] at hh
    have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hNp) hNp.le
    nlinarith only [hh,hl,hNR]
  have hb := mul_le_mul_of_nonneg_left (abs_le.mp hbL).1 (show (0 : ℝ)≤alpha N by positivity)
  have hs'' := mul_le_mul_of_nonneg_left (abs_le.mp hsL).2 (show (0 : ℝ)≤2*alpha N by positivity)
  have hp := mul_le_mul_of_nonneg_left hpL (show (0 : ℝ)≤(N : ℝ)-1 by linarith)
  have htwo := mul_le_mul_of_nonneg_left h2L (show 0≤(N : ℝ)*((N : ℝ)-1) by exact mul_nonneg hNp.le (by linarith))
  have haL := mul_le_mul_of_nonneg_right ha (show 0≤L by linarith)
  have hlog2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  rw [log_norm_centralDensity Bn rootBn s (by omega) hB hr hs]
  push_cast
  rw [hnm]
  nlinarith only [hb,hs'',hp,htwo,haL,(abs_le.mp hrL).2,hlogN,hfac,hlog2,hL,hNR]

end
end IsingBulk.Anisotropic.NegativeDominance
