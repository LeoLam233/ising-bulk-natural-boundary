import IsingBulk.Anisotropic.NegativeDominance.PhysicalMiddleSum

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

theorem entropyPart_quadratic_lower (n : ℕ) (hn : 2≤n) :
    entropyPart 2-5*(n : ℝ)^2 ≤ entropyPart n := by
  have h := (entropyPart_step_bounds 2 (n-2) (by omega)).1
  have he : 2+(n-2)=n := by omega
  rw [he] at h
  have hcast : ((n-2 : ℕ) : ℝ)=(n : ℝ)-2 := by rw [Nat.cast_sub hn]; norm_num
  rw [hcast] at h
  norm_num at h
  have hnn : (0 : ℝ)≤n := by positivity
  nlinarith only [h, hnn]

def growthLoss (B0 : ℂ) (s A C : ℝ) : ℝ :=
  A*(8+|modelQuadraticConstant B0 s|+Real.log Real.pi)+
    |entropyPart 2|+|modelAdditiveConstant B0|+C+Real.log (Real.pi^2/2)

/-- A quantitative root-growth lower bound for the exact model. Its analytic
error hypothesis is subsequently discharged by the physical analytic branch. -/
theorem log_norm_model_growth (B0 Bn rootBn H : ℂ) (s A C : ℝ) (n j : ℕ)
    (hn : 2≤n) (ho : Odd n) (hj : alpha n<j) (hjH : j≤n^3)
    (hlog : 1≤Real.log n) (_hA : 0≤A) (hC : 0≤C)
    (hscale : (n : ℝ)^2*Real.log n≤A*(j : ℝ))
    (hB : Bn≠0) (hr : rootBn≠0) (hh : H≠0) (hs : s≠0) (hsq : rootBn^2=Bn)
    (herr : |modelAnalyticError B0 Bn H n|≤C) :
    (j : ℝ)*(2*Real.log n-growthLoss B0 s A C) ≤
      Real.log ‖model Bn rootBn H s n j‖ := by
  have hjpos : 0<j := by omega
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hjpos
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have hpi : 0≤Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogj : Real.log (j : ℝ)≤3*Real.log n := by
    have h := Real.log_le_log (by exact_mod_cast hjpos : (0 : ℝ)<j)
      (by exact_mod_cast hjH : (j : ℝ)≤(n : ℝ)^3)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have haa := two_mul_alpha_add_one n ho
  have haR : 2*(alpha n : ℝ)+1=(n : ℝ)^2 := by
    exact_mod_cast (haa.trans (pow_two n).symm)
  have haN : (alpha n : ℝ)≤(n : ℝ)^2 := by
    nlinarith only [haR, (show (0 : ℝ)≤alpha n by positivity)]
  have hq := neg_abs_le (modelQuadraticConstant B0 s)
  have hterm : -(n : ℝ)^2*(|modelQuadraticConstant B0 s|+3*Real.log n) ≤
      (alpha n : ℝ)*(modelQuadraticConstant B0 s-Real.log j) := by
    have h1 := mul_le_mul_of_nonneg_left
      (show -|modelQuadraticConstant B0 s|-3*Real.log n ≤ modelQuadraticConstant B0 s-Real.log j by linarith only [hq,hlogj])
      (show (0 : ℝ)≤alpha n by positivity)
    have h2 := mul_le_mul_of_nonpos_right haN
      (show -|modelQuadraticConstant B0 s|-3*Real.log n≤0 by nlinarith only [abs_nonneg (modelQuadraticConstant B0 s), hlog])
    nlinarith only [h1,h2]
  have htau := (log_tau_error_bounds n hn).1
  have ht := mul_nonneg (show (0 : ℝ)≤j by positivity) htau
  have hpcoef : ((n : ℝ)-1)/2≤(n : ℝ)^2 := by nlinarith only [hnR]
  have hp := mul_le_mul_of_nonneg_right hpcoef hpi
  have he := entropyPart_quadratic_lower n hn
  have hg := (gammaCorrection_step_bounds 0 (alpha n) (j : ℝ) (by simpa using (show (alpha n : ℝ)<j by exact_mod_cast hj))).1
  simp only [zero_add, gammaCorrection, cumulative, Finset.range_zero, Finset.sum_empty, sub_zero] at hg
  have hg' : 0≤gammaCorrection (alpha n) j := hg
  have hN : (n : ℝ)^2≤A*(j : ℝ) :=
    (le_mul_of_one_le_right (sq_nonneg _) hlog).trans hscale
  have hcost := mul_le_mul_of_nonneg_right hN
    (show 0≤5+|modelQuadraticConstant B0 s|+Real.log Real.pi by positivity)
  have hconstant := mul_le_mul_of_nonneg_right hjR
    (show 0≤|entropyPart 2|+|modelAdditiveConstant B0|+C by positivity)
  have hdecomp := log_norm_model_decomposition B0 Bn rootBn H s n j (by omega) ho hj hB hr hh hs hsq
  have herrL := (abs_le.mp herr).1
  have he0 := neg_abs_le (entropyPart 2)
  have hd0 := neg_abs_le (modelAdditiveConstant B0)
  unfold growthLoss
  nlinarith only [hdecomp, hterm, ht, hp, he, hg', hcost, hscale, hconstant, herrL, he0, hd0]

end
end IsingBulk.Anisotropic.NegativeDominance
