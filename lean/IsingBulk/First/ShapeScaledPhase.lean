import IsingBulk.First.MeanShapeGap
import IsingBulk.First.JointPoleRegularity

/-! Actual one-variable regular phase along epsilon=lam², u=lam*tau.
This is the source branch, not a quadratic replacement model. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Set Filter
open scoped Topology

def scaledShapeW (a : OrderedChartData) (tau lam : ℂ) : ℂ :=
  complexRadialTrace a.theta (lam^2) - Complex.cos (lam*tau-(a.alpha:ℂ))

def scaledShapePhase (a : OrderedChartData) (tau lam : ℂ) : ℂ :=
  lowerArccos (scaledShapeW a tau lam)

theorem complexRadialTrace_analytic_zero (theta : ℝ) :
    AnalyticAt ℂ (complexRadialTrace theta) 0 := by
  have hf : AnalyticAt ℂ (fun e : ℂ => (1+e)*Complex.exp ((theta:ℂ)*Complex.I)) 0 := by fun_prop
  exact hf.add (hf.inv (by simp))

theorem scaledShapeW_zero (a : OrderedChartData) (tau : ℂ) :
    scaledShapeW a tau 0 = (Real.cos a.beta:ℂ) := by
  have h := a.angle_relation
  simp only [scaledShapeW, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_sub,
    Complex.cos_neg, ← Complex.ofReal_cos, complexRadialTrace_zero]
  exact_mod_cast (show 2*Real.cos a.theta-Real.cos a.alpha=Real.cos a.beta by linarith)

theorem scaledShapePhase_zero (a : OrderedChartData) (tau : ℂ) :
    scaledShapePhase a tau 0 = (a.beta:ℂ) := by
  rw [scaledShapePhase, scaledShapeW_zero]
  exact lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt, Real.pi_pos])

theorem scaledShapeW_analytic_zero (a : OrderedChartData) (tau : ℂ) :
    AnalyticAt ℂ (scaledShapeW a tau) 0 := by
  have hT := complexRadialTrace_analytic_zero a.theta
  have hp : AnalyticAt ℂ (fun lam : ℂ => lam^2) 0 := by fun_prop
  have ht : AnalyticAt ℂ (fun lam : ℂ => complexRadialTrace a.theta (lam^2)) 0 :=
    AnalyticAt.comp (f := fun lam : ℂ => lam^2) (g := complexRadialTrace a.theta)
      (by simpa using hT) hp
  exact ht.sub (by fun_prop)

theorem scaledShapePhase_analytic_zero (a : OrderedChartData) (tau : ℂ) :
    AnalyticAt ℂ (scaledShapePhase a tau) 0 := by
  have ho := lowerArccos_analytic_cos a.beta a.beta_pos a.beta_lt
  rw [← scaledShapeW_zero a tau] at ho
  exact ho.comp (scaledShapeW_analytic_zero a tau)

theorem scaledShapePhase_eq_radialResiduePhase (a : OrderedChartData) (tau lam : ℂ) :
    scaledShapePhase a tau lam = radialResiduePhase a (lam^2) (lam*tau) := rfl

theorem scaledShapeW_hasDerivAt_zero (a : OrderedChartData) (tau : ℂ) :
    HasDerivAt (scaledShapeW a tau) (-(Real.sin a.alpha:ℂ)*tau) 0 := by
  have hpow : HasDerivAt (fun lam : ℂ => lam^2) 0 0 := by
    simpa using! (hasDerivAt_id (0:ℂ)).pow 2
  have ht := (complexRadialTrace_hasDerivAt_zero a.theta).comp_of_eq 0 hpow (by simp)
  have hc := (((hasDerivAt_id (0:ℂ)).mul_const tau).sub_const (a.alpha:ℂ)).ccos
  convert ht.sub hc using 1
  · rfl
  · simp

theorem scaledShapeW_deriv_near_zero (a : OrderedChartData) (tau : ℂ) :
    deriv (scaledShapeW a tau) =ᶠ[𝓝 (0:ℂ)] (fun lam =>
      deriv (complexRadialTrace a.theta) (lam^2)*(2*lam) +
        Complex.sin (lam*tau-(a.alpha:ℂ))*tau) := by
  have he : ∀ᶠ lam : ℂ in 𝓝 0, AnalyticAt ℂ (complexRadialTrace a.theta) (lam^2) := by
    have h := (complexRadialTrace_analytic_zero a.theta).eventually_analyticAt
    have ht : Tendsto (fun lam : ℂ => lam^2) (𝓝 0) (𝓝 0) := by
      simpa using (show ContinuousAt (fun lam : ℂ => lam^2) 0 by fun_prop).tendsto
    exact ht.eventually h
  filter_upwards [he] with lam hlam
  have ht := hlam.differentiableAt.hasDerivAt.comp lam ((hasDerivAt_id lam).pow 2)
  have hc := (((hasDerivAt_id lam).mul_const tau).sub_const (a.alpha:ℂ)).ccos
  have h : HasDerivAt (scaledShapeW a tau)
      (deriv (complexRadialTrace a.theta) (lam^2)*(2*lam) +
        Complex.sin (lam*tau-(a.alpha:ℂ))*tau) lam := by
    convert ht.sub hc using 1
    · rfl
    · simp
  exact h.deriv

theorem scaledShapeW_second_hasDerivAt_zero (a : OrderedChartData) (tau : ℂ) :
    HasDerivAt (deriv (scaledShapeW a tau))
      (4*Complex.I*(Real.sin a.theta:ℂ)+(Real.cos a.alpha:ℂ)*tau^2) 0 := by
  have hpow : HasDerivAt (fun lam : ℂ => lam^2) 0 0 := by
    simpa using! (hasDerivAt_id (0:ℂ)).pow 2
  have ht := (complexRadialTrace_analytic_zero a.theta).deriv.differentiableAt.hasDerivAt.comp_of_eq
    0 hpow (by simp)
  have hlin := (hasDerivAt_id (0:ℂ)).const_mul (2:ℂ)
  have hsin := ((((hasDerivAt_id (0:ℂ)).mul_const tau).sub_const (a.alpha:ℂ)).csin).mul_const tau
  have h := (ht.mul hlin).add hsin
  have h' : HasDerivAt (fun lam : ℂ => deriv (complexRadialTrace a.theta) (lam^2)*(2*lam) +
      Complex.sin (lam*tau-(a.alpha:ℂ))*tau)
      (4*Complex.I*(Real.sin a.theta:ℂ)+(Real.cos a.alpha:ℂ)*tau^2) 0 := by
    convert h using 1
    · rfl
    · simp [complexRadialTrace_hasDerivAt_zero a.theta |>.deriv]
      ring
  exact h'.congr_of_eventuallyEq (scaledShapeW_deriv_near_zero a tau)

theorem scaledShapePhase_hasDerivAt_zero (a : OrderedChartData) (tau : ℂ) :
    HasDerivAt (scaledShapePhase a tau) ((a.b:ℂ)*tau) 0 := by
  have ho := lowerArccos_hasDerivAt_regular (Real.cos a.beta:ℂ)
    (lowerArccos_analytic_cos a.beta a.beta_pos a.beta_lt)
  have h := ho.comp_of_eq 0 (scaledShapeW_hasDerivAt_zero a tau) (scaledShapeW_zero a tau).symm
  convert h using 1
  · rfl
  · rw [lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt, Real.pi_pos])]
    simp [OrderedChartData.b, Complex.ofReal_div, Complex.ofReal_sin]
    ring

theorem scaledShapePhase_deriv_near_zero (a : OrderedChartData) (tau : ℂ) :
    deriv (scaledShapePhase a tau) =ᶠ[𝓝 (0:ℂ)]
      (fun lam => -deriv (scaledShapeW a tau) lam / Complex.sin (scaledShapePhase a tau lam)) := by
  have ha := scaledShapePhase_analytic_zero a tau
  have hw := scaledShapeW_analytic_zero a tau
  have hs : Complex.sin (scaledShapePhase a tau 0) ≠ 0 := by
    rw [scaledShapePhase_zero, ← Complex.ofReal_sin]
    exact_mod_cast a.sin_beta_pos.ne'
  have hc := Complex.continuous_sin.continuousAt.comp ha.continuousAt
  filter_upwards [ha.eventually_analyticAt, hw.eventually_analyticAt, hc.eventually_ne hs] with lam hp hW hsin
  have hd := hp.differentiableAt.hasDerivAt
  have hcos := hd.ccos
  have hfun : (fun z => Complex.cos (scaledShapePhase a tau z)) = scaledShapeW a tau :=
    funext fun z => cos_lowerArccos _
  rw [hfun] at hcos
  have he := hcos.unique hW.differentiableAt.hasDerivAt
  change Complex.sin (scaledShapePhase a tau lam) ≠ 0 at hsin
  apply (eq_div_iff hsin).mpr
  linear_combination -he

theorem scaledShapePhase_second_hasDerivAt_zero (a : OrderedChartData) (tau : ℂ) :
    HasDerivAt (deriv (scaledShapePhase a tau))
      (-2*Complex.I*(a.A₀ 0 : ℂ)-2*(a.d : ℂ)*tau^2) 0 := by
  have hs : (Real.sin a.beta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr a.sin_beta_pos.ne'
  have hb : (Real.sin a.alpha : ℂ) = (a.b : ℂ)*(Real.sin a.beta : ℂ) := by
    simp only [OrderedChartData.b, Complex.ofReal_div]
    field_simp
  have hcurv : -((Real.cos a.alpha : ℂ)+(Real.cos a.beta : ℂ)*(a.b : ℂ)^2) /
      (Real.sin a.beta : ℂ) = -2*(a.d : ℂ) := by
    exact_mod_cast a.curvature_identity
  have hcoef :
      (-(4*Complex.I*(Real.sin a.theta : ℂ)+(Real.cos a.alpha : ℂ)*tau^2)*
        (Real.sin a.beta : ℂ) - ((Real.sin a.alpha : ℂ)*tau)*
          ((Real.cos a.beta : ℂ)*((a.b : ℂ)*tau))) / (Real.sin a.beta : ℂ)^2 =
        -2*Complex.I*(a.A₀ 0 : ℂ)-2*(a.d : ℂ)*tau^2 := by
    calc
      _ = -(4*Complex.I*(Real.sin a.theta : ℂ))/(Real.sin a.beta : ℂ) +
          (-((Real.cos a.alpha : ℂ)+(Real.cos a.beta : ℂ)*(a.b : ℂ)^2)/
            (Real.sin a.beta : ℂ))*tau^2 := by
              rw [hb]
              field_simp
              ring
      _ = _ := by
        rw [hcurv]
        simp only [OrderedChartData.A₀, zero_mul, sub_zero, Complex.ofReal_div,
          Complex.ofReal_mul, Complex.ofReal_ofNat]
        ring
  have hnum := (scaledShapeW_second_hasDerivAt_zero a tau).neg
  have hsin := (scaledShapePhase_hasDerivAt_zero a tau).csin
  have hsn : Complex.sin (scaledShapePhase a tau 0) ≠ 0 := by
    rw [scaledShapePhase_zero, ← Complex.ofReal_sin]
    exact hs
  have hq := hnum.div hsin hsn
  simp only [Pi.neg_apply, scaledShapePhase_zero, (scaledShapeW_hasDerivAt_zero a tau).deriv,
    neg_mul, neg_neg, ← Complex.ofReal_sin, ← Complex.ofReal_cos] at hq
  have hq' : HasDerivAt
      (fun lam => -deriv (scaledShapeW a tau) lam / Complex.sin (scaledShapePhase a tau lam))
      (-2*Complex.I*(a.A₀ 0 : ℂ)-2*(a.d : ℂ)*tau^2) 0 := by
    convert hq using 1
    simpa only [neg_mul] using hcoef.symm
  exact hq'.congr_of_eventuallyEq (scaledShapePhase_deriv_near_zero a tau)

end
end IsingBulk.First
