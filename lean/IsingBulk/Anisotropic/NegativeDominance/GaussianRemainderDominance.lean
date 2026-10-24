import IsingBulk.Anisotropic.NegativeDominance.GaussianMoment
import IsingBulk.Anisotropic.NegativeDominance.HighRangeDominance

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

/-- The summed analytic and annular errors have smaller exponential order
than even the already controlled high-range envelope. -/
theorem eventually_gaussian_moment_le_high (C : ℝ) :
    ∀ᶠ j : ℕ in atTop,
      ((j : ℝ)+1)/2*Real.log ((j : ℝ)+2)+C*((j : ℝ)+1)≤
        (j : ℝ)*Real.log j-j*Real.sqrt (Real.log j)/32 := by
  have ht : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,
    ht.eventually (eventually_ge_atTop (max 1 (8*(|Real.log 2|+2*|C|))))] with j hj hl
  have hjR : (2 : ℝ)≤j := by exact_mod_cast hj
  have hl1 : 1≤Real.log (j : ℝ) := (le_max_left _ _).trans hl
  have hlC : 8*(|Real.log 2|+2*|C|)≤Real.log (j : ℝ) := (le_max_right _ _).trans hl
  have hjp : (0 : ℝ)<j := by linarith
  have hlog := Real.log_le_log (show 0<(j : ℝ)+2 by positivity) (show (j : ℝ)+2≤2*j by linarith)
  rw [Real.log_mul (by norm_num) hjp.ne'] at hlog
  have hlog0 : 0≤Real.log ((j : ℝ)+2) := Real.log_nonneg (by linarith)
  have hcoef : ((j : ℝ)+1)/2≤3/4*(j : ℝ) := by linarith
  have hshape := mul_le_mul hcoef hlog hlog0 (show 0≤3/4*(j : ℝ) by positivity)
  have hCt := mul_le_mul_of_nonneg_left (le_abs_self C) (show 0≤(j : ℝ)+1 by positivity)
  have hCt' := mul_le_mul_of_nonneg_left (show (j : ℝ)+1≤2*j by linarith) (abs_nonneg C)
  have hsq := Real.sq_sqrt (show 0≤Real.log (j : ℝ) by linarith)
  have hs := Real.sqrt_nonneg (Real.log (j : ℝ))
  have hsle : Real.sqrt (Real.log (j : ℝ))≤Real.log (j : ℝ) := by nlinarith
  have hsprod := mul_le_mul_of_nonneg_left hsle hjp.le
  have hCprod := mul_le_mul_of_nonneg_left hlC hjp.le
  have hl2prod := mul_le_mul_of_nonneg_left (le_abs_self (Real.log 2)) hjp.le
  have hl2abs : 0≤(j : ℝ)*|Real.log 2| := by positivity
  have hlogprod : 0≤(j : ℝ)*Real.log j := mul_nonneg hjp.le (by linarith)
  nlinarith only [hshape,hCt,hCt',hsprod,hCprod,hl2prod,hl2abs,hlogprod]

/-- The same centered integer order controls all Gaussian remainder sums. -/
theorem physical_gaussian_on_crossing_range
    (B rootB : ℂ→ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ),rootB t^2=B t) (hphi : Real.sin phi≠0)
    (q : ℕ) (D C : ℝ) (hD : 0<D) :
    ∃N : ℕ,∀n≥N,Odd n → ∀j : ℕ,
      lowerCrossingOrder n-1<(j : ℝ) → (j : ℝ)≤upperCrossingOrder n → n≤j →
      D*Real.exp (((j : ℝ)+1)/2*Real.log ((j : ℝ)+2)+C*((j : ℝ)+1))≤
        Real.exp (-(n : ℝ))*‖physicalModel B rootB phi (n+2*q) j‖ := by
  obtain ⟨N,hN⟩ := physical_high_on_crossing_range B rootB phi hB hB0 hroot hroot0 hsq hphi q D hD
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (eventually_gaussian_moment_le_high C)
  refine ⟨max N J,fun n hn ho j hjL hjH hnj => ?_⟩
  apply le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hJ j (by omega))) hD.le)
  exact hN n (by omega) ho j hjL hjH hnj

end
end IsingBulk.Anisotropic.NegativeDominance
