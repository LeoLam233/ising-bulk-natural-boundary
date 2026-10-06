import IsingBulk.First.MeanRadialPhase

/-! Actual radial-center Taylor remainder and its O(epsilon²) real-phase
error, including the radius-independent post-residue specialization c₀=0. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch
open scoped Topology

theorem radialRegularPhase_analytic_radial (a : OrderedChartData) (c₀ : ℝ) :
    AnalyticAt ℂ (fun e => radialRegularPhase a c₀ e 0) 0 := by
  have hz : ((1+(0:ℂ))*Complex.exp ((a.theta:ℂ)*Complex.I)) ≠ 0 := by simp
  have hS : AnalyticAt ℂ (complexRadialTrace a.theta) 0 := by
    unfold complexRadialTrace
    exact ((analyticAt_const.add analyticAt_id).mul analyticAt_const).add
      (((analyticAt_const.add analyticAt_id).mul analyticAt_const).inv hz)
  have hW : AnalyticAt ℂ (fun e => radialRegularW a c₀ e 0) 0 := by
    unfold radialRegularW
    exact hS.sub (by fun_prop)
  have ho := lowerArccos_analytic_cos a.beta a.beta_pos a.beta_lt
  rw [← radialRegularW_zero a c₀] at ho
  exact AnalyticAt.comp (f := fun e => radialRegularW a c₀ e 0) (g := lowerArccos) ho hW

theorem radial_center_taylor (a : OrderedChartData) (c₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ e in 𝓝 (0:ℂ),
      ‖radialRegularPhase a c₀ e 0-(a.beta:ℂ)+Complex.I*(a.A₀ c₀:ℂ)*e‖ ≤ C*‖e‖^2 := by
  obtain ⟨C,hC,hb⟩ := analytic_quadratic_remainder
    (fun e => radialRegularPhase a c₀ e 0) (radialRegularPhase_analytic_radial a c₀)
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with e he
  rw [radialRegularPhase_zero, fderiv_eq_deriv_mul, (radialRegularPhase_radial_derivative a c₀).deriv] at he
  convert he using 1
  congr 1
  ring

/-- Only a quadratic real error remains at the radial center. -/
theorem radial_center_phase_error (a : OrderedChartData) (c₀ : ℝ) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ epsilon : ℝ, |epsilon| < r →
      |(radialRegularPhase a c₀ (epsilon:ℂ) 0).re-a.beta| ≤ C*epsilon^2 := by
  obtain ⟨C,hC,hb⟩ := radial_center_taylor a c₀
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hb
  refine ⟨C,r,hC,hr,?_⟩
  intro epsilon he
  have hh := hball (y := (epsilon:ℂ)) (by simpa [dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using he)
  have hre := Complex.abs_re_le_norm
    (radialRegularPhase a c₀ (epsilon:ℂ) 0-(a.beta:ℂ)+Complex.I*(a.A₀ c₀:ℂ)*(epsilon:ℂ))
  have hn : |(radialRegularPhase a c₀ (epsilon:ℂ) 0).re-a.beta| ≤
      ‖radialRegularPhase a c₀ (epsilon:ℂ) 0-(a.beta:ℂ)+Complex.I*(a.A₀ c₀:ℂ)*(epsilon:ℂ)‖ := by
    simpa using hre
  apply hn.trans
  simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hh

end
end IsingBulk.First
