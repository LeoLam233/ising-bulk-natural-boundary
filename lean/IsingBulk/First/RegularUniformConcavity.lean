import IsingBulk.First.RegularAngularDerivatives

/-! Sign-independent regular phase foundation for the actual source. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set IsingBulk.Branch
open scoped Topology BigOperators

theorem regularMeanSecond_at_selected_regular (a : RegularChartData) :
    regularMeanSecond ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ) a.alpha 0 = ((-2*a.d:ℝ):ℂ) := by
  have hp : regularMeanPhase ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ) a.alpha 0 = (a.beta:ℂ) := by
    unfold regularMeanPhase
    simp only [zero_sub, Complex.cos_neg, ← Complex.ofReal_cos, Complex.ofReal_add,
      add_sub_cancel_left]
    exact lowerArccos_cos a.beta a.beta_pos a.beta_lt_pi
  unfold regularMeanSecond
  rw [hp]
  simp only [zero_sub, Complex.cos_neg, Complex.sin_neg, neg_sq, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.ofReal_add, add_sub_cancel_left]
  have hh := a.curvature_identity
  unfold RegularChartData.b at hh
  have he : -(Real.cos a.alpha)/Real.sin a.beta -
      (Real.sin a.alpha)^2*Real.cos a.beta/(Real.sin a.beta)^3 = -2*a.d := by
    rw [← hh]
    field_simp [ne_of_gt a.sin_beta_pos]
    ring
  exact_mod_cast he

def radialResiduePhase (a : RegularChartData) (epsilon u : ℂ) : ℂ :=
  regularMeanPhase (complexRadialTrace a.theta epsilon) a.alpha u

def radialResidueSecond (a : RegularChartData) (x : ℝ × ℝ) : ℂ :=
  regularMeanSecond (complexRadialTrace a.theta (x.1:ℂ)) a.alpha (x.2:ℂ)

theorem radialResiduePhase_eq_radialRegularPhase (a : RegularChartData) (epsilon u : ℂ) :
    radialResiduePhase a epsilon u = radialRegularPhase a 0 epsilon u := by
  simp [radialResiduePhase, regularMeanPhase, radialRegularPhase, radialRegularW, Complex.cosh_mul_I]

theorem radialResiduePhase_zero (a : RegularChartData) : radialResiduePhase a 0 0 = (a.beta:ℂ) := by
  rw [radialResiduePhase_eq_radialRegularPhase, radialRegularPhase_zero]

theorem radialResidueSecond_zero (a : RegularChartData) : radialResidueSecond a 0 = ((-2*a.d:ℝ):ℂ) := by
  unfold radialResidueSecond
  simp only [Prod.fst_zero, Prod.snd_zero, Complex.ofReal_zero, complexRadialTrace_zero]
  have he : (2:ℂ)*(Real.cos a.theta:ℂ) = ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ) := by
    exact_mod_cast a.angle_relation.symm
  rw [he, regularMeanSecond_at_selected_regular]

theorem radialResidueSecond_continuous (a : RegularChartData) : ContinuousAt (radialResidueSecond a) 0 := by
  have hT : ContinuousAt (fun x : ℝ × ℝ => complexRadialTrace a.theta (x.1:ℂ)) 0 := by
    exact ContinuousAt.comp (g := complexRadialTrace a.theta) (f := fun x : ℝ × ℝ => (x.1:ℂ))
      (by simpa using (complexRadialTrace_hasDerivAt_zero a.theta).continuousAt) (by fun_prop)
  have hW : ContinuousAt (fun x : ℝ × ℝ =>
      complexRadialTrace a.theta (x.1:ℂ)-Complex.cos ((x.2:ℂ)-(a.alpha:ℂ))) 0 := by
    exact hT.sub (by fun_prop)
  have hW0 : complexRadialTrace a.theta ((0:ℝ × ℝ).1:ℂ)-
      Complex.cos (((0:ℝ × ℝ).2:ℂ)-(a.alpha:ℂ)) = (Real.cos a.beta:ℂ) := by
    have he := a.angle_relation
    simp [complexRadialTrace_zero]
    exact_mod_cast (show 2*Real.cos a.theta-Real.cos a.alpha=Real.cos a.beta by linarith)
  have hp : ContinuousAt (fun x : ℝ × ℝ => radialResiduePhase a (x.1:ℂ) (x.2:ℂ)) 0 := by
    have ho := (lowerArccos_analytic_cos_of_lt_pi a.beta a.beta_pos a.beta_lt_pi).continuousAt
    rw [← hW0] at ho
    exact ContinuousAt.comp (g := lowerArccos)
      (f := fun x : ℝ × ℝ => complexRadialTrace a.theta (x.1:ℂ)-Complex.cos ((x.2:ℂ)-(a.alpha:ℂ))) ho hW
  have hs : Complex.sin (radialResiduePhase a 0 0) ≠ 0 := by
    rw [radialResiduePhase_zero, ← Complex.ofReal_sin]
    exact_mod_cast ne_of_gt a.sin_beta_pos
  have hsin : ContinuousAt (fun x : ℝ × ℝ => Complex.sin (radialResiduePhase a (x.1:ℂ) (x.2:ℂ))) 0 :=
    Complex.continuous_sin.continuousAt.comp hp
  change ContinuousAt (fun x : ℝ × ℝ =>
    -Complex.cos ((x.2:ℂ)-(a.alpha:ℂ))/Complex.sin (radialResiduePhase a (x.1:ℂ) (x.2:ℂ)) -
      Complex.sin ((x.2:ℂ)-(a.alpha:ℂ))^2 *
        (complexRadialTrace a.theta (x.1:ℂ)-Complex.cos ((x.2:ℂ)-(a.alpha:ℂ))) /
        Complex.sin (radialResiduePhase a (x.1:ℂ) (x.2:ℂ))^3) 0
  exact ((by fun_prop : ContinuousAt (fun x : ℝ × ℝ => -Complex.cos ((x.2:ℂ)-(a.alpha:ℂ))) 0).div
    hsin (by simpa using hs)).sub
    (((by fun_prop : ContinuousAt (fun x : ℝ × ℝ => Complex.sin ((x.2:ℂ)-(a.alpha:ℂ))^2) 0).mul hW).div
      (hsin.pow 3) (by simpa using pow_ne_zero 3 hs))

/-- Curvature is controlled with its actual sign. No sign of cos(beta) is assumed. -/
theorem radialResidueSecond_signed_negative (a : RegularChartData) :
    ∃ r : ℝ, 0 < r ∧ ∀ epsilon u : ℝ, |epsilon| < r → |u| < r →
      a.curvatureSign*(radialResidueSecond a (epsilon,u)).re ≤ -|a.d| := by
  have hc : ContinuousAt (fun x => a.curvatureSign*(radialResidueSecond a x).re) 0 :=
    continuousAt_const.mul (Complex.continuous_re.continuousAt.comp (radialResidueSecond_continuous a))
  have he : ∀ᶠ x in 𝓝 (0:ℝ × ℝ), a.curvatureSign*(radialResidueSecond a x).re < -|a.d| :=
    hc.eventually_lt continuousAt_const (by
      rw [radialResidueSecond_zero]
      simp only [Complex.ofReal_re]
      nlinarith [a.curvatureSign_mul_d, abs_pos.mpr a.d_ne_zero])
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r,hr,?_⟩
  intro epsilon u he hu
  exact (hball (by simpa [dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using And.intro he hu)).le

end
end IsingBulk.First.Regular
