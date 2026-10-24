import IsingBulk.Anisotropic.NegativeDominance.CentralDensityEntropy
import IsingBulk.Anisotropic.NegativeDominance.HigherWindingBeta

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

def higherWindingOverhead (M c : ℝ) (Bn rootBn H : ℂ) (s : ℝ) (N : ℕ) : ℝ :=
  M^(1+alpha N+N+N.choose 2)/(c*N)*‖H‖^(alpha N)/‖centralDensity Bn rootBn s N‖

theorem higherWindingOverhead_entropy (M c : ℝ) (Bn rootBn H : ℂ) (s L : ℝ) {N : ℕ}
    (hN : 2≤N) (hM : 1≤M) (hc : 0<c) (hB : Bn≠0) (hr : rootBn≠0) (hH : H≠0)
    (hs : s≠0) (hL : 1≤L) (hML : Real.log M≤L) (hcL : |Real.log c|≤L)
    (hbL : |Real.log ‖Bn‖|≤L) (hrL : |Real.log ‖rootBn‖|≤L)
    (hHL : Real.log ‖H‖≤L) (hsL : |Real.log (|s|)|≤L)
    (hpL : Real.log (2*Real.pi)≤L) (h2L : Real.log 2≤L) :
    higherWindingOverhead M c Bn rootBn H s N≤Real.exp (20*(L+1)*(N : ℝ)^2) := by
  have hMp : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hNR : (2 : ℝ)≤N := by exact_mod_cast hN
  have hNp : (0 : ℝ)<N := by linarith
  have hnorm : 0<‖centralDensity Bn rootBn s N‖ :=
    norm_pos_iff.mpr (centralDensity_ne_zero Bn rootBn s (by omega) hB hr hs)
  have hhn : 0<‖H‖ := norm_pos_iff.mpr hH
  have hcentral := centralDensity_log_lower Bn rootBn s L hN hB hr hs hL hbL hrL hsL hpL h2L
  have haNat : alpha N≤N*N := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have ha : (alpha N : ℝ)≤(N : ℝ)^2 := by exact_mod_cast (show alpha N≤N^2 by simpa only [pow_two] using haNat)
  have hchoose := Nat.cast_choose_two (K := ℝ) N
  have he : ((1+alpha N+N+N.choose 2 : ℕ) : ℝ)≤3*(N : ℝ)^2 := by
    push_cast
    nlinarith only [ha,hchoose,hNR]
  have heM : ((1+alpha N+N+N.choose 2 : ℕ) : ℝ)*Real.log M≤3*(N : ℝ)^2*L :=
    (mul_le_mul_of_nonneg_left hML (by positivity)).trans
      (mul_le_mul_of_nonneg_right he (by linarith))
  have heH : (alpha N : ℝ)*Real.log ‖H‖≤(N : ℝ)^2*L :=
    (mul_le_mul_of_nonneg_left hHL (by positivity)).trans
      (mul_le_mul_of_nonneg_right ha (by linarith))
  have hlN : 0≤Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  have hLc : L≤L*(N : ℝ)^2 := le_mul_of_one_le_right (by linarith) (by nlinarith only [hNR])
  have hLp : 0≤L*(N : ℝ)^2 := by positivity
  have hc' := (abs_le.mp hcL).1
  apply (Real.log_le_iff_le_exp (by unfold higherWindingOverhead; positivity)).mp
  unfold higherWindingOverhead
  rw [Real.log_div (by positivity) hnorm.ne',Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),Real.log_pow,Real.log_mul hc.ne' hNp.ne',Real.log_pow]
  nlinarith only [heM,heH,hlN,hc',hcentral,hNR,hL,hLc,hLp,sq_nonneg (N : ℝ)]

/-- Actual beta majorant divided by the exact first-winding model. -/
theorem higher_winding_beta_model_bound (M c : ℝ) (Bn rootBn H : ℂ) (s : ℝ)
    {N j : ℕ} (ho : Odd N) (hN : 3≤N) (hj : 4*alpha N≤j)
    (hM : 0≤M) (hc : 0<c) (hB : Bn≠0) (hr : rootBn≠0) (hH : H≠0) (hs : s≠0)
    {u : ℝ} (hu : 2*tau N≤u) :
    (2*M^(1+alpha N+N+N.choose 2)/(c*N))*constrainedBetaValue N j u (1/(4*(N : ℝ)))≤
      higherWindingOverhead M c Bn rootBn H s N*(1/2 : ℝ)^(j/2)*‖model Bn rootBn H s N j‖ := by
  have hb := higher_winding_beta_suppression (by omega : 0<N) hj hu
  have hh := mul_le_mul_of_nonneg_left hb
    (show 0≤2*M^(1+alpha N+N+N.choose 2)/(c*N) by positivity)
  rw [first_beta_value_eq_model_norm Bn rootBn H s ho hN j (by omega) hB hr hH hs] at hh
  convert hh using 1
  unfold higherWindingOverhead
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
