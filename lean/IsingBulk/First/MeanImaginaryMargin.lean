import IsingBulk.First.MeanLocalDomain
import IsingBulk.First.MeanPhase
import IsingBulk.Analysis.BranchInclusion

/-! Uniform positive imaginary dispersion margin on the actual radial
regular chart, before and throughout its downward mean motion. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch
open scoped Topology

def meanDampingCoefficient (a : OrderedChartData) (c₀ : ℝ) (x : ℝ × ℝ) : ℝ :=
  (2-x.1/(1+x.1))*Real.sin a.theta +
    c₀*sinhQuotient (-c₀*x.1)*Real.sin (-a.alpha+x.2)

theorem meanDampingCoefficient_zero (a : OrderedChartData) (c₀ : ℝ) :
    meanDampingCoefficient a c₀ 0 = a.A₀ c₀*Real.sin a.beta := by
  simp only [meanDampingCoefficient, Prod.fst_zero, Prod.snd_zero, add_zero,
    zero_div, sub_zero, mul_zero, sinhQuotient_zero, mul_one, Real.sin_neg]
  unfold OrderedChartData.A₀
  field_simp [ne_of_gt a.sin_beta_pos]
  ring

theorem meanDampingCoefficient_continuous (a : OrderedChartData) (c₀ : ℝ) :
    ContinuousAt (meanDampingCoefficient a c₀) 0 := by
  have hh : ContinuousAt (fun x : ℝ × ℝ => sinhQuotient (-c₀*x.1)) 0 := by
    exact ContinuousAt.comp (g := sinhQuotient) (f := fun x : ℝ × ℝ => -c₀*x.1)
      (by simpa using sinhQuotient_continuous) (by fun_prop)
  unfold meanDampingCoefficient
  fun_prop (disch := norm_num)

theorem radial_chart_imaginary_factorization (a : OrderedChartData) (c₀ epsilon u : ℝ)
    (he : 1+epsilon ≠ 0) :
    (IsingBulk.Jets.chartW (radialParameter a.theta epsilon) (-c₀*epsilon) a.alpha (u:ℂ)).im =
      epsilon*meanDampingCoefficient a c₀ (epsilon,u) := by
  have him := (radial_trace_components a.theta epsilon he).2
  have hs := sinhQuotient_identity (-c₀*epsilon)
  unfold IsingBulk.Jets.chartW IsingBulk.Jets.angularY
  rw [show ((-c₀*epsilon:ℝ):ℂ)+((u:ℂ)-(a.alpha:ℂ))*Complex.I =
    ((-c₀*epsilon:ℝ):ℂ)+(((-a.alpha+u:ℝ):ℂ))*Complex.I by push_cast; ring]
  rw [polar_dispersion_im, him, ← hs]
  unfold meanDampingCoefficient
  ring

/-- Constants are chosen before epsilon and the angular deviation. -/
theorem radial_chart_imaginary_margin (a : OrderedChartData) (c₀ : ℝ)
    (hA : 0 < a.A₀ c₀) :
    ∃ r : ℝ, 0 < r ∧ ∀ epsilon u : ℝ,
      0 < epsilon → epsilon < r → |u| < r →
      (a.A₀ c₀*Real.sin a.beta/2)*epsilon ≤
        (IsingBulk.Jets.chartW (radialParameter a.theta epsilon) (-c₀*epsilon) a.alpha (u:ℂ)).im := by
  have hpos : 0 < a.A₀ c₀*Real.sin a.beta := mul_pos hA a.sin_beta_pos
  have hc := meanDampingCoefficient_continuous a c₀
  have he : ∀ᶠ x in 𝓝 (0:ℝ × ℝ), a.A₀ c₀*Real.sin a.beta/2 < meanDampingCoefficient a c₀ x :=
    continuousAt_const.eventually_lt hc (by rw [meanDampingCoefficient_zero]; linarith)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r,hr,?_⟩
  intro epsilon u hε hεr hu
  have hx : dist (epsilon,u) (0:ℝ × ℝ) < r := by
    simpa [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, abs_of_pos hε] using And.intro hεr hu
  have hh := hball hx
  rw [radial_chart_imaginary_factorization a c₀ epsilon u (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hh.le hε.le]

end
end IsingBulk.First
