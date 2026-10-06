import IsingBulk.First.MeanRegularPhase
import IsingBulk.Analysis.BranchInclusion

/-! Actual logarithmic lower-phase attenuation on a compact regular arc.
Unlike branch-point estimates, this uses only the regular base beta. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch
open scoped Topology

theorem exists_sinh_linear_upper :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, 0 ≤ x → x < r → Real.sinh x ≤ 2*x := by
  have he : ∀ᶠ x in 𝓝 (0:ℝ), sinhQuotient x < 2 :=
    sinhQuotient_continuous.eventually_lt continuousAt_const
      (by rw [sinhQuotient_zero]; norm_num)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r,hr,?_⟩
  intro x hx hxr
  have hq := hball (show dist x 0 < r by simpa [Real.dist_eq, abs_of_nonneg hx] using hxr)
  rw [← sinhQuotient_identity]
  nlinarith [mul_le_mul_of_nonneg_left hq.le hx]

/-- The same actual phase as the mean chart loses a controlled amount of
modulus. The neighborhood is fixed before the damped W is supplied. -/
theorem regular_phase_attenuation (a : OrderedChartData) :
    ∃ r : ℝ, 0 < r ∧ ∀ W : ℂ,
      ‖W-(Real.cos a.beta:ℂ)‖ < r → 0 < W.re → 0 < W.im →
      W.im/2 ≤ -(lowerArccos W).im := by
  obtain ⟨eta,heta,hsinh⟩ := exists_sinh_linear_upper
  have hc : ContinuousAt (fun W : ℂ => |(lowerArccos W).im|) (Real.cos a.beta:ℂ) :=
    ((Complex.continuous_im.continuousAt).comp
      (lowerArccos_analytic_cos a.beta a.beta_pos a.beta_lt).continuousAt).abs
  have hsmall : ∀ᶠ W in 𝓝 (Real.cos a.beta:ℂ), |(lowerArccos W).im| < eta :=
    hc.eventually_lt continuousAt_const (by
      rw [lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt, Real.pi_pos])]
      simpa using heta)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hsmall
  refine ⟨r,hr,?_⟩
  intro W hW hWr hWi
  have hphi := (lowerArccos_sheet W hWr hWi).2.2.2
  have ha0 : 0 ≤ -(lowerArccos W).im := by linarith
  have hasmall : -(lowerArccos W).im < eta := by
    have hh := hball (show dist W (Real.cos a.beta:ℂ) < r by simpa [dist_eq_norm] using hW)
    rwa [abs_of_neg hphi] at hh
  have hs := hsinh (-(lowerArccos W).im) ha0 hasmall
  have hcos := congrArg Complex.im (cos_lowerArccos W)
  rw [Complex.cos_eq] at hcos
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_sinh, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, mul_one, sub_zero, add_zero, zero_sub] at hcos
  have hspos : 0 ≤ Real.sinh (-(lowerArccos W).im) := Real.sinh_nonneg_iff.mpr ha0
  have hsin := Real.sin_le_one (lowerArccos W).re
  have hmul := mul_le_mul_of_nonneg_right hsin hspos
  rw [Real.sinh_neg] at hs hmul
  nlinarith

end
end IsingBulk.First
