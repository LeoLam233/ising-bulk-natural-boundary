import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
# F002: differential identities and the regular one-body factor

These identities are derived from the local dispersion equation and an
actual differentiable inverse.  They do not construct the global
one-sided inverse or select its branch.  At a branch point the literal
singular quotient is replaced by the displayed analytic regular factor;
no equality of Lean's totalized `0/0` with that extension is asserted.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology

/-- Differentiate the actual local dispersion with respect to `v = U + φ`. -/
theorem inverse_coordinate_derivative (U : ℂ → ℂ) (S v u' : ℂ)
    (hU : HasDerivAt U u' v)
    (hdisp : (fun z => Complex.cos (U z) + Complex.cos (z - U z)) =ᶠ[𝓝 v]
      (fun _ => S))
    (hden : Complex.sin (v - U v) - Complex.sin (U v) ≠ 0) :
    u' = Complex.sin (v - U v) /
      (Complex.sin (v - U v) - Complex.sin (U v)) := by
  have hc : HasDerivAt (fun z => Complex.cos (U z) + Complex.cos (z - U z))
      (-Complex.sin (U v) * u' - Complex.sin (v - U v) * (1 - u')) v := by
    simpa only [Pi.add_apply, Pi.sub_apply, id_eq, sub_eq_add_neg, neg_mul] using!
      hU.ccos.add (((hasDerivAt_id v).sub hU).ccos)
  have hzero : HasDerivAt (fun z => Complex.cos (U z) + Complex.cos (z - U z)) 0 v :=
    (hasDerivAt_const v S).congr_of_eventuallyEq hdisp
  have heq := hc.unique hzero
  apply (eq_div_iff hden).2
  linear_combination heq

/-- At fixed `v`, differentiating the physical dispersion yields `U_S`. -/
theorem inverse_parameter_derivative (U : ℂ → ℂ) (S v u' : ℂ)
    (hU : HasDerivAt U u' S)
    (hdisp : (fun z => Complex.cos (U z) + Complex.cos (v - U z)) =ᶠ[𝓝 S] id)
    (hden : Complex.sin (v - U S) - Complex.sin (U S) ≠ 0) :
    u' = 1 / (Complex.sin (v - U S) - Complex.sin (U S)) := by
  have hc : HasDerivAt (fun z => Complex.cos (U z) + Complex.cos (v - U z))
      (-Complex.sin (U S) * u' + Complex.sin (v - U S) * u') S := by
    simpa only [Pi.add_apply, Pi.sub_apply, zero_sub, mul_neg, neg_mul, neg_neg] using!
      hU.ccos.add (((hasDerivAt_const S v).sub hU).ccos)
  have hid : HasDerivAt (fun z => Complex.cos (U z) + Complex.cos (v - U z)) 1 S :=
    (hasDerivAt_id S).congr_of_eventuallyEq hdisp
  have heq := hc.unique hid
  apply (eq_div_iff hden).2
  linear_combination heq

/-- Exact discriminant of the regular inverse; this fixes the square-root square
without choosing a branch of that square root. -/
theorem inverse_denominator_square (w φ S : ℂ)
    (hdisp : Complex.cos φ + Complex.cos w = S) :
    (Complex.sin φ - Complex.sin w) ^ 2 =
      4 * Complex.cos ((φ + w) / 2) ^ 2 - S ^ 2 := by
  rw [← hdisp, Complex.sin_sub_sin, Complex.cos_add_cos]
  linear_combination
    4 * Complex.cos ((φ + w) / 2) ^ 2 * Complex.sin_sq_add_cos_sq ((φ - w) / 2)

/-- Analytic expression of the regularized one-body factor in inverse coordinates. -/
def regularOneBody (w φ : ℂ) : ℂ := -Complex.I / (Complex.sin φ - Complex.sin w)

/-- Off the branch, the regularized expression equals the original one-body quotient. -/
theorem regularOneBody_eq_quotient (w φ : ℂ)
    (hφ : Complex.sin φ ≠ 0) (hden : Complex.sin φ - Complex.sin w ≠ 0) :
    (Complex.sin φ / (Complex.sin φ - Complex.sin w)) /
      Complex.sinh (Complex.I * φ) = regularOneBody w φ := by
  rw [mul_comm Complex.I φ, Complex.sinh_mul_I]
  unfold regularOneBody
  field_simp [hφ, hden, Complex.I_ne_zero]
  simp [Complex.I_sq]

/-- The displayed extension is analytic whenever its regular inverse denominator is nonzero. -/
theorem regularOneBody_analyticAt (U : ℂ → ℂ) (v : ℂ)
    (hU : AnalyticAt ℂ U v)
    (hden : Complex.sin (v - U v) - Complex.sin (U v) ≠ 0) :
    AnalyticAt ℂ (fun z => regularOneBody (U z) (z - U z)) v := by
  unfold regularOneBody
  exact analyticAt_const.div
    ((Complex.analyticAt_sin.comp (analyticAt_id.sub hU)).sub
      (Complex.analyticAt_sin.comp hU)) hden

end IsingBulk.AnisoF002.Isotropic
