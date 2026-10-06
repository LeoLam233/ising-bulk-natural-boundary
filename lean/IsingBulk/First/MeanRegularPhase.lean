import IsingBulk.First.MeanPhase
import IsingBulk.Analysis.RegularCoordinates
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Analytic regularity at the actual selected alpha/beta chart, including
its undamped boundary center. This is distinct from branch-point geometry. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch
open scoped Topology

/-- The explicit upper inverse root is exp(i beta) at a regular real center. -/
theorem inverseCosineRoot_cos (beta : ℝ) (hb : 0 < beta) (hb' : beta < Real.pi) :
    inverseCosineRoot (Real.cos beta : ℂ) = Complex.exp ((beta:ℂ)*Complex.I) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hb hb'
  have hsq : (1-(Real.cos beta:ℂ)^2) = ((Real.sin beta)^2:ℝ) := by
    have h := Real.sin_sq_add_cos_sq beta
    push_cast
    exact_mod_cast (show 1-(Real.cos beta)^2 = (Real.sin beta)^2 by linarith)
  rw [inverseCosineRoot, hsq, sqrt_ofReal_nonnegative _ (sq_nonneg _), Real.sqrt_sq hs.le,
    Complex.exp_ofReal_mul_I]
  ring

theorem lowerArccos_cos (beta : ℝ) (hb : 0 < beta) (hb' : beta < Real.pi) :
    lowerArccos (Real.cos beta : ℂ) = (beta:ℂ) := by
  unfold lowerArccos
  rw [inverseCosineRoot_cos beta hb hb', Complex.log_exp]
  · ring_nf
    simp [Complex.I_sq]
  · simpa using (show -Real.pi < beta by linarith [Real.pi_pos])
  · simpa using hb'.le

/-- Explicit slit-plane conditions give actual analyticity of the frozen
logarithmic branch, including W real in (0,1). -/
theorem lowerArccos_analytic_regular (W : ℂ)
    (hs : 1-W^2 ∈ Complex.slitPlane)
    (hl : inverseCosineRoot W ∈ Complex.slitPlane) : AnalyticAt ℂ lowerArccos W := by
  have hsqrt : AnalyticAt ℂ Complex.sqrt (1-W^2) :=
    Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hs)
  have hpoly : AnalyticAt ℂ (fun z : ℂ => 1-z^2) W := by fun_prop
  have hroot : AnalyticAt ℂ inverseCosineRoot W :=
    analyticAt_id.add (analyticAt_const.mul (AnalyticAt.comp
      (f := fun z : ℂ => 1-z^2) (g := Complex.sqrt) hsqrt hpoly))
  have hlog : AnalyticAt ℂ Complex.log (inverseCosineRoot W) :=
    analyticAt_clog hl
  exact analyticAt_const.mul (AnalyticAt.comp
    (f := inverseCosineRoot) (g := Complex.log) hlog hroot)

theorem lowerArccos_analytic_cos (beta : ℝ) (hb : 0 < beta) (hb' : beta < Real.pi / 2) :
    AnalyticAt ℂ lowerArccos (Real.cos beta : ℂ) := by
  apply lowerArccos_analytic_regular
  · left
    have hs := Real.sin_pos_of_pos_of_lt_pi hb (by linarith [Real.pi_pos])
    have hsq := Real.sin_sq_add_cos_sq beta
    simp only [Complex.sub_re, Complex.one_re, ← Complex.ofReal_pow, Complex.ofReal_re]
    nlinarith [sq_pos_of_pos hs]
  · left
    rw [inverseCosineRoot_cos beta hb (by linarith [Real.pi_pos])]
    simpa using Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hb'⟩

/-- The derivative identity follows from the actual cosine equation and
analyticity; it does not assume a derivative of an abstract substitute. -/
theorem lowerArccos_hasDerivAt_regular (W : ℂ) (h : AnalyticAt ℂ lowerArccos W) :
    HasDerivAt lowerArccos (-1 / Complex.sin (lowerArccos W)) W := by
  have hd := h.differentiableAt.hasDerivAt
  have hc := hd.ccos
  have heq : (fun z => Complex.cos (lowerArccos z)) = id := funext cos_lowerArccos
  rw [heq] at hc
  have hv := hc.unique (hasDerivAt_id W)
  have hn : Complex.sin (lowerArccos W) ≠ 0 := by
    intro hz
    simp [hz] at hv
  convert hd using 1
  symm
  apply (eq_div_iff hn).mpr
  linear_combination -hv

/-- The literal zero-radius, fixed-source angular phase. -/
def centralChartPhase (a : OrderedChartData) (u : ℂ) : ℂ :=
  lowerArccos ((Real.cos a.alpha + Real.cos a.beta : ℝ) - Complex.cos (u-(a.alpha:ℂ)))

theorem centralChartPhase_zero (a : OrderedChartData) : centralChartPhase a 0 = (a.beta:ℂ) := by
  simp only [centralChartPhase, zero_sub, Complex.cos_neg, ← Complex.ofReal_cos,
    Complex.ofReal_add, add_sub_cancel_left]
  exact lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt, Real.pi_pos])

theorem centralChartPhase_hasDerivAt_zero (a : OrderedChartData) :
    HasDerivAt (centralChartPhase a) (a.b:ℂ) 0 := by
  have hw : ((Real.cos a.alpha + Real.cos a.beta : ℝ) : ℂ) -
      Complex.cos (0-(a.alpha:ℂ)) = (Real.cos a.beta:ℂ) := by simp
  have hi : HasDerivAt
      (fun u : ℂ => ((Real.cos a.alpha + Real.cos a.beta : ℝ):ℂ) - Complex.cos (u-(a.alpha:ℂ)))
      (-(Real.sin a.alpha:ℂ)) 0 := by
    convert (((hasDerivAt_id (0:ℂ)).sub_const (a.alpha:ℂ)).ccos).const_sub
      ((Real.cos a.alpha + Real.cos a.beta:ℝ):ℂ) using 1 <;> simp
  have ho := lowerArccos_hasDerivAt_regular (Real.cos a.beta:ℂ)
    (lowerArccos_analytic_cos a.beta a.beta_pos a.beta_lt)
  have hh := ho.comp_of_eq 0 hi hw.symm
  change HasDerivAt (centralChartPhase a) _ 0 at hh
  convert hh using 1
  rw [lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt, Real.pi_pos])]
  simp [OrderedChartData.b, Complex.ofReal_div, Complex.ofReal_sin]
  ring

end
end IsingBulk.First
