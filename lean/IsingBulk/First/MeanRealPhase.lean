import IsingBulk.First.MeanUniformConcavity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! The exact real angular derivatives used for constrained shape concavity.
Complex derivative identities are restricted only after neighborhood equality. -/
namespace IsingBulk.First
noncomputable section
open Complex
open scoped Topology

def realRegularMeanPhase (T : ℂ) (alpha : ℝ) (u : ℝ) : ℝ :=
  (regularMeanPhase T alpha (u:ℂ)).re

theorem regularMeanPhase_analyticAt (T : ℂ) (alpha : ℝ) (u : ℂ)
    (hr : 0 < (T-Complex.cos (u-(alpha:ℂ))).re)
    (hi : 0 < (T-Complex.cos (u-(alpha:ℂ))).im) :
    AnalyticAt ℂ (regularMeanPhase T alpha) u := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [regularMeanPhase_quadrant_near T alpha u hr hi] with v hv
  exact (regularMeanPhase_hasDerivAt T alpha v hv.1 hv.2).differentiableAt

theorem realRegularMeanPhase_hasDerivAt (T : ℂ) (alpha u : ℝ)
    (hr : 0 < (T-Complex.cos ((u:ℂ)-(alpha:ℂ))).re)
    (hi : 0 < (T-Complex.cos ((u:ℂ)-(alpha:ℂ))).im) :
    HasDerivAt (realRegularMeanPhase T alpha) (deriv (regularMeanPhase T alpha) (u:ℂ)).re u := by
  have hp := regularMeanPhase_hasDerivAt T alpha (u:ℂ) hr hi
  have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hp.comp_ofReal
  simpa only [Function.comp_def, Complex.reCLM_apply, hp.deriv, realRegularMeanPhase] using! hh

theorem realRegularMeanPhase_second_hasDerivAt (T : ℂ) (alpha u : ℝ)
    (hr : 0 < (T-Complex.cos ((u:ℂ)-(alpha:ℂ))).re)
    (hi : 0 < (T-Complex.cos ((u:ℂ)-(alpha:ℂ))).im) :
    HasDerivAt (deriv (realRegularMeanPhase T alpha)) (regularMeanSecond T alpha (u:ℂ)).re u := by
  have hp := regularMeanPhase_second_hasDerivAt T alpha (u:ℂ) hr hi
  have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hp.comp_ofReal
  have hc : ContinuousAt (fun v : ℝ => T-Complex.cos ((v:ℂ)-(alpha:ℂ))) u := by fun_prop
  have hne : ∀ᶠ v : ℝ in 𝓝 u,
      0 < (T-Complex.cos ((v:ℂ)-(alpha:ℂ))).re ∧
      0 < (T-Complex.cos ((v:ℂ)-(alpha:ℂ))).im :=
    (continuousAt_const.eventually_lt (Complex.continuous_re.continuousAt.comp hc) hr).and
    (continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp hc) hi)
  have he : deriv (realRegularMeanPhase T alpha) =ᶠ[𝓝 u]
      (fun v : ℝ => (deriv (regularMeanPhase T alpha) (v:ℂ)).re) := by
    filter_upwards [hne] with v hv
    exact (realRegularMeanPhase_hasDerivAt T alpha v hv.1 hv.2).deriv
  exact hh.congr_of_eventuallyEq he

theorem realRegularMeanPhase_analyticAt (T : ℂ) (alpha u : ℝ)
    (hr : 0 < (T-Complex.cos ((u:ℂ)-(alpha:ℂ))).re)
    (hi : 0 < (T-Complex.cos ((u:ℂ)-(alpha:ℂ))).im) :
    AnalyticAt ℝ (realRegularMeanPhase T alpha) u :=
  (regularMeanPhase_analyticAt T alpha (u:ℂ) hr hi).re_ofReal

end
end IsingBulk.First
