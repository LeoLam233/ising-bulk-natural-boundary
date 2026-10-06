import IsingBulk.First.MeanRealPhase
import IsingBulk.First.MeanImaginaryMargin
import IsingBulk.First.MeanAttenuation

/-! Fixed regular domains and attenuation for the actual radius-free phase
after the Y residue. All neighborhood sizes precede epsilon and u. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch
open scoped Topology

def radialResidueW (a : OrderedChartData) (x : ℝ × ℝ) : ℂ :=
  complexRadialTrace a.theta (x.1:ℂ)-Complex.cos ((x.2:ℂ)-(a.alpha:ℂ))

theorem radialResidueW_zero (a : OrderedChartData) : radialResidueW a 0 = (Real.cos a.beta:ℂ) := by
  have he := a.angle_relation
  simp [radialResidueW, complexRadialTrace_zero]
  exact_mod_cast (show 2*Real.cos a.theta-Real.cos a.alpha=Real.cos a.beta by linarith)

theorem radialResidueW_continuous (a : OrderedChartData) : ContinuousAt (radialResidueW a) 0 := by
  have hT : ContinuousAt (fun x : ℝ × ℝ => complexRadialTrace a.theta (x.1:ℂ)) 0 :=
    ContinuousAt.comp (g := complexRadialTrace a.theta) (f := fun x : ℝ × ℝ => (x.1:ℂ))
      (by simpa using (complexRadialTrace_hasDerivAt_zero a.theta).continuousAt) (by fun_prop)
  exact hT.sub (by fun_prop)

theorem radialResidueW_eq_chartW (a : OrderedChartData) (epsilon u : ℝ) :
    radialResidueW a (epsilon,u) =
      IsingBulk.Jets.chartW (radialParameter a.theta epsilon) 0 a.alpha (u:ℂ) := by
  rw [IsingBulk.Jets.chartW_eq_plateauW]
  simp [radialResidueW, complexRadialTrace, plateauW, radialParameter, Complex.cosh_mul_I]
  congr 1
  ring

theorem A₀_zero_pos (a : OrderedChartData) : 0 < a.A₀ 0 := by
  unfold OrderedChartData.A₀
  simpa using div_pos (mul_pos (by norm_num : (0:ℝ)<2) a.sin_theta_pos) a.sin_beta_pos

/-- Uniform actual W-quadrant and closeness, including the positive epsilon margin. -/
theorem radialResidueW_domain (a : OrderedChartData) {eta : ℝ} (heta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∀ epsilon u : ℝ, 0 < epsilon → epsilon < r → |u| < r →
      0 < (radialResidueW a (epsilon,u)).re ∧ 0 < (radialResidueW a (epsilon,u)).im ∧
        ‖radialResidueW a (epsilon,u)-(Real.cos a.beta:ℂ)‖ < eta := by
  obtain ⟨rM,hrM,hM⟩ := radial_chart_imaginary_margin a 0 (A₀_zero_pos a)
  have hc := radialResidueW_continuous a
  have hreal : ∀ᶠ x in 𝓝 (0:ℝ × ℝ), 0 < (radialResidueW a x).re :=
    continuousAt_const.eventually_lt (Complex.continuous_re.continuousAt.comp hc)
      (by rw [radialResidueW_zero]; exact a.cos_beta_pos)
  have hdist : ∀ᶠ x in 𝓝 (0:ℝ × ℝ), ‖radialResidueW a x-(Real.cos a.beta:ℂ)‖ < eta :=
    (hc.sub_const (Real.cos a.beta:ℂ)).norm.eventually_lt continuousAt_const
      (by rw [radialResidueW_zero, sub_self, norm_zero]; exact heta)
  obtain ⟨rC,hrC,hC⟩ := Metric.eventually_nhds_iff.mp (hreal.and hdist)
  refine ⟨min rM rC, lt_min hrM hrC, ?_⟩
  intro epsilon u he her hu
  have hrc : dist (epsilon,u) (0:ℝ × ℝ) < rC := by
    simpa [dist_zero_right, Prod.norm_def, Real.norm_eq_abs, abs_of_pos he] using
      And.intro (her.trans_le (min_le_right _ _)) (hu.trans_le (min_le_right _ _))
  have hc' := hC hrc
  have hm := hM epsilon u he (her.trans_le (min_le_left _ _)) (hu.trans_le (min_le_left _ _))
  have hpos : 0 < (a.A₀ 0*Real.sin a.beta/2)*epsilon := by
    have hA := A₀_zero_pos a
    have hb := a.sin_beta_pos
    positivity
  refine ⟨hc'.1, ?_, hc'.2⟩
  rw [radialResidueW_eq_chartW]
  simpa using hpos.trans_le hm

/-- Fixed phase closeness, hence an eventual no-wrapping neighborhood. -/
theorem radialResiduePhase_near (a : OrderedChartData) {eta : ℝ} (heta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∀ epsilon u : ℝ, 0 < epsilon → epsilon < r → |u| < r →
      ‖radialResiduePhase a (epsilon:ℂ) (u:ℂ)-(a.beta:ℂ)‖ < eta := by
  have hc := (lowerArccos_analytic_cos a.beta a.beta_pos a.beta_lt).continuousAt
  have he : ∀ᶠ W in 𝓝 (Real.cos a.beta:ℂ), ‖lowerArccos W-(a.beta:ℂ)‖ < eta :=
    (hc.sub_const (a.beta:ℂ)).norm.eventually_lt continuousAt_const (by
      rw [lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt, Real.pi_pos]), sub_self, norm_zero]
      exact heta)
  obtain ⟨etaW,hetaW,hW⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨r,hr,hD⟩ := radialResidueW_domain a hetaW
  refine ⟨r,hr,?_⟩
  intro epsilon u he her hu
  exact hW (by simpa [dist_eq_norm, radialResidueW] using! (hD epsilon u he her hu).2.2)

/-- Linear attenuation for the actual post-residue phase on a fixed angular arc. -/
theorem radialResiduePhase_attenuation (a : OrderedChartData) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ epsilon u : ℝ,
      0 < epsilon → epsilon < r → |u| < r →
      c*epsilon ≤ -(radialResiduePhase a (epsilon:ℂ) (u:ℂ)).im := by
  obtain ⟨eta,heta,hatt⟩ := regular_phase_attenuation a
  obtain ⟨rD,hrD,hD⟩ := radialResidueW_domain a heta
  obtain ⟨rM,hrM,hM⟩ := radial_chart_imaginary_margin a 0 (A₀_zero_pos a)
  let c := a.A₀ 0*Real.sin a.beta/4
  have hc : 0 < c := by dsimp [c]; exact div_pos (mul_pos (A₀_zero_pos a) a.sin_beta_pos) (by norm_num)
  refine ⟨c,min rD rM,hc,lt_min hrD hrM,?_⟩
  intro epsilon u he her hu
  have hd := hD epsilon u he (her.trans_le (min_le_left _ _)) (hu.trans_le (min_le_left _ _))
  have ha := hatt (radialResidueW a (epsilon,u)) hd.2.2 hd.1 hd.2.1
  have hm := hM epsilon u he (her.trans_le (min_le_right _ _)) (hu.trans_le (min_le_right _ _))
  simp only [neg_zero, zero_mul] at hm
  rw [← radialResidueW_eq_chartW] at hm
  change _ ≤ -(radialResiduePhase a (epsilon:ℂ) (u:ℂ)).im at ha
  dsimp [c]
  linarith

end
end IsingBulk.First
