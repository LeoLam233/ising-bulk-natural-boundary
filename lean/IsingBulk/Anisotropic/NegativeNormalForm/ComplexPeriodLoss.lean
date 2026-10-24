import IsingBulk.Anisotropic.NegativeNormalForm.PhysicalComplexPeriod
import IsingBulk.Anisotropic.NegativeNormalForm.BetaUniformScale

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Filter
open scoped Topology

theorem complex_norm_re_ratio_le_exp (z : ℂ) (hz : (1:ℝ)/2≤z.re) :
    ‖z‖/z.re≤Real.exp (2*‖z-1‖^2) := by
  have hre := Complex.re_le_norm z
  have he := Complex.sq_norm_sub_sq_re (z-1)
  simp only [Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,sub_zero] at he
  have him : z.im^2≤‖z-1‖^2 := by nlinarith [sq_nonneg (z.re-1)]
  have hez := Complex.sq_norm_sub_sq_re z
  have hdiff : ‖z‖-z.re≤‖z-1‖^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hre) (show 0≤‖z‖+z.re-1 by linarith)]
  have hratio : ‖z‖/z.re≤1+2*‖z-1‖^2 := by
    apply (div_le_iff₀ (by linarith : 0<z.re)).2
    nlinarith [mul_nonneg (sq_nonneg ‖z-1‖) (show 0≤2*z.re-1 by linarith)]
  exact hratio.trans (by simpa [add_comm] using Real.add_one_le_exp (2*‖z-1‖^2))

open IsingBulk.Anisotropic.NegativeDominance in
/-- The actual complex-kernel normalization loss is quartic in the angle.
In particular, it is uniformly bounded on the growing central sequence. -/
theorem centralHessian_period_loss (B : ℂ → ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ n : ℕ, 3≤n → ∀ d : ℂ, ‖d‖<r →
      (1:ℝ)/2≤(centralHessian B phi d).re ∧
      (‖centralHessian B phi d‖/(centralHessian B phi d).re)^(alpha n)≤
        Real.exp (L^2*(n:ℝ)^2*‖d‖^4) := by
  obtain ⟨L,hL,hquad⟩ := centralHessian_quadratic_bound B phi hB
  have hc : Tendsto (centralHessian B phi) (𝓝 (0:ℂ)) (𝓝 (1:ℂ)) := by
    simpa only [ContinuousAt,centralHessian_zero] using (centralHessian_analyticAt_zero B phi hB).continuousAt
  have hnear : ∀ᶠ d in 𝓝 (0:ℂ), ‖centralHessian B phi d-1‖<1/2 := by
    have he := hc (Metric.ball_mem_nhds (1:ℂ) (by norm_num : (0:ℝ)<1/2))
    change ∀ᶠ d in 𝓝 (0:ℂ), dist (centralHessian B phi d) 1<1/2 at he
    simpa only [dist_eq_norm] using he
  obtain ⟨r,hr,he⟩ := Metric.eventually_nhds_iff.mp (hquad.and hnear)
  refine ⟨r,L,hr,hL,?_⟩
  intro n hn d hd
  obtain ⟨hq,hnear⟩ := he (by simpa using hd)
  have hre : (1:ℝ)/2≤(centralHessian B phi d).re := by
    have hh := Complex.re_le_norm (1-centralHessian B phi d)
    rw [norm_sub_rev] at hh
    simp only [Complex.sub_re,Complex.one_re] at hh
    linarith
  refine ⟨hre,?_⟩
  have hpow := pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (by linarith))
    (complex_norm_re_ratio_le_exp _ hre) (alpha n)
  rw [←Real.exp_nat_mul] at hpow
  have hsq : ‖centralHessian B phi d-1‖^2≤L^2*‖d‖^4 := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hq 2
    nlinarith
  have han := (alpha_pos_and_twice_le n hn).2
  have hanR : 2*(alpha n:ℝ)≤(n:ℝ)^2 := by exact_mod_cast (show 2*alpha n≤n^2 by simpa [pow_two] using han)
  apply hpow.trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (n:ℝ)^2*‖centralHessian B phi d-1‖^2 := by nlinarith [mul_le_mul_of_nonneg_right hanR (sq_nonneg ‖centralHessian B phi d-1‖)]
    _ ≤ (n:ℝ)^2*(L^2*‖d‖^4) := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = _ := by ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
