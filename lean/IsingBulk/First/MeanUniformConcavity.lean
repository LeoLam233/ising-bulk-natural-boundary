import IsingBulk.First.MeanRegularDerivatives

/-! A fixed neighborhood on which the actual explicit angular second
coefficient retains the strictly negative regular-center sign. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch
open scoped Topology

def radialResiduePhase (a : OrderedChartData) (epsilon u : ℂ) : ℂ :=
  regularMeanPhase (complexRadialTrace a.theta epsilon) a.alpha u

def radialResidueSecond (a : OrderedChartData) (x : ℝ × ℝ) : ℂ :=
  regularMeanSecond (complexRadialTrace a.theta (x.1:ℂ)) a.alpha (x.2:ℂ)

theorem radialResiduePhase_eq_radialRegularPhase (a : OrderedChartData) (epsilon u : ℂ) :
    radialResiduePhase a epsilon u = radialRegularPhase a 0 epsilon u := by
  simp [radialResiduePhase, regularMeanPhase, radialRegularPhase, radialRegularW, Complex.cosh_mul_I]

theorem radialResiduePhase_zero (a : OrderedChartData) : radialResiduePhase a 0 0 = (a.beta:ℂ) := by
  rw [radialResiduePhase_eq_radialRegularPhase, radialRegularPhase_zero]

theorem radialResidueSecond_zero (a : OrderedChartData) : radialResidueSecond a 0 = ((-2*a.d:ℝ):ℂ) := by
  unfold radialResidueSecond
  simp only [Prod.fst_zero, Prod.snd_zero, Complex.ofReal_zero, complexRadialTrace_zero]
  have he : (2:ℂ)*(Real.cos a.theta:ℂ) = ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ) := by
    exact_mod_cast a.angle_relation.symm
  rw [he, regularMeanSecond_at_selected]

theorem radialResidueSecond_continuous (a : OrderedChartData) : ContinuousAt (radialResidueSecond a) 0 := by
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
    have ho := (lowerArccos_analytic_cos a.beta a.beta_pos a.beta_lt).continuousAt
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

/-- The same fixed radius works before epsilon and the shape angle vary. -/
theorem radialResidueSecond_negative (a : OrderedChartData) :
    ∃ r : ℝ, 0 < r ∧ ∀ epsilon u : ℝ, |epsilon| < r → |u| < r →
      (radialResidueSecond a (epsilon,u)).re ≤ -a.d := by
  have hc : ContinuousAt (fun x => (radialResidueSecond a x).re) 0 :=
    Complex.continuous_re.continuousAt.comp (radialResidueSecond_continuous a)
  have he : ∀ᶠ x in 𝓝 (0:ℝ × ℝ), (radialResidueSecond a x).re < -a.d :=
    hc.eventually_lt continuousAt_const (by
      rw [radialResidueSecond_zero]
      simp only [Complex.ofReal_re]
      linarith [a.d_pos])
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r,hr,?_⟩
  intro epsilon u he hu
  exact (hball (by simpa [dist_zero_right, Prod.norm_def, Real.norm_eq_abs] using And.intro he hu)).le

end
end IsingBulk.First
