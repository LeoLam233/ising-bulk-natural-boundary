import IsingBulk.First.MeanRegularPhase

/-! The actual second angular derivative at the selected regular center.
The first derivative is identified on a neighborhood before differentiation. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch
open scoped Topology

theorem centralChartPhase_cos (a : OrderedChartData) (u : ℂ) :
    Complex.cos (centralChartPhase a u) =
      ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ)-Complex.cos (u-(a.alpha:ℂ)) :=
  cos_lowerArccos _

theorem centralChartPhase_analytic_zero (a : OrderedChartData) :
    AnalyticAt ℂ (centralChartPhase a) 0 := by
  have hin : AnalyticAt ℂ
      (fun u : ℂ => ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ)-Complex.cos (u-(a.alpha:ℂ))) 0 := by
    fun_prop
  have hout := lowerArccos_analytic_cos a.beta a.beta_pos a.beta_lt
  have he : ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ)-Complex.cos (0-(a.alpha:ℂ)) =
      (Real.cos a.beta:ℂ) := by simp
  rw [← he] at hout
  exact AnalyticAt.comp (f := fun u : ℂ =>
    ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ)-Complex.cos (u-(a.alpha:ℂ)))
    (g := lowerArccos) hout hin

theorem centralChartPhase_hasDerivAt_of_analytic (a : OrderedChartData) (u : ℂ)
    (hf : AnalyticAt ℂ (centralChartPhase a) u)
    (hs : Complex.sin (centralChartPhase a u) ≠ 0) :
    HasDerivAt (centralChartPhase a)
      (-Complex.sin (u-(a.alpha:ℂ))/Complex.sin (centralChartPhase a u)) u := by
  have hd := hf.differentiableAt.hasDerivAt
  have hh := hd.ccos
  have he : (fun z => Complex.cos (centralChartPhase a z)) =
      (fun z => ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ)-Complex.cos (z-(a.alpha:ℂ))) :=
    funext (centralChartPhase_cos a)
  rw [he] at hh
  have hi := (((hasDerivAt_id u).sub_const (a.alpha:ℂ)).ccos).const_sub
    ((Real.cos a.alpha+Real.cos a.beta:ℝ):ℂ)
  have hval := hh.unique hi
  convert hd using 1
  symm
  apply (eq_div_iff hs).mpr
  simp only [neg_neg, mul_one, id_eq] at hval
  linear_combination -hval

theorem centralChartPhase_deriv_near_zero (a : OrderedChartData) :
    deriv (centralChartPhase a) =ᶠ[𝓝 0]
      (fun u => -Complex.sin (u-(a.alpha:ℂ))/Complex.sin (centralChartPhase a u)) := by
  have ha := centralChartPhase_analytic_zero a
  have hs : Complex.sin (centralChartPhase a 0) ≠ 0 := by
    rw [centralChartPhase_zero, ← Complex.ofReal_sin]
    exact_mod_cast ne_of_gt a.sin_beta_pos
  have hc : ContinuousAt (fun u => Complex.sin (centralChartPhase a u)) 0 :=
    Complex.continuous_sin.continuousAt.comp ha.continuousAt
  have he : ∀ᶠ u in 𝓝 (0:ℂ), Complex.sin (centralChartPhase a u) ≠ 0 :=
    hc.eventually_ne hs
  filter_upwards [ha.eventually_analyticAt, he] with u hau hsu
  exact (centralChartPhase_hasDerivAt_of_analytic a u hau hsu).deriv

/-- The source curvature is the actual complex angular second derivative. -/
theorem centralChartPhase_second_hasDerivAt (a : OrderedChartData) :
    HasDerivAt (deriv (centralChartPhase a)) ((-2*a.d:ℝ):ℂ) 0 := by
  have hfirst := centralChartPhase_hasDerivAt_zero a
  have hsin := hfirst.csin
  rw [centralChartPhase_zero, ← Complex.ofReal_cos] at hsin
  have hnum : HasDerivAt (fun u : ℂ => -Complex.sin (u-(a.alpha:ℂ)))
      (-(Real.cos a.alpha:ℂ)) 0 := by
    simpa using! (((hasDerivAt_id (0:ℂ)).sub_const (a.alpha:ℂ)).csin).neg
  have hs : Complex.sin (centralChartPhase a 0) ≠ 0 := by
    rw [centralChartPhase_zero, ← Complex.ofReal_sin]
    exact_mod_cast ne_of_gt a.sin_beta_pos
  have hquot := hnum.div hsin hs
  have hc : (-(Real.cos a.alpha)*Real.sin a.beta-
      Real.sin a.alpha*(Real.cos a.beta*a.b))/(Real.sin a.beta)^2 = -2*a.d := by
    rw [← a.curvature_identity]
    unfold OrderedChartData.b
    field_simp [ne_of_gt a.sin_beta_pos]
    ring
  have hcoef :
      (-(Real.cos a.alpha:ℂ)*Complex.sin (centralChartPhase a 0)-
        (-Complex.sin (0-(a.alpha:ℂ)))*((Real.cos a.beta:ℂ)*(a.b:ℂ))) /
        Complex.sin (centralChartPhase a 0)^2 = ((-2*a.d:ℝ):ℂ) := by
    simp only [centralChartPhase_zero, zero_sub, Complex.sin_neg, neg_neg,
      ← Complex.ofReal_sin]
    exact_mod_cast hc
  rw [hcoef] at hquot
  exact hquot.congr_of_eventuallyEq (centralChartPhase_deriv_near_zero a)

end
end IsingBulk.First
