import IsingBulk.Anisotropic.NegativeNormalForm.SeparableEnergy
import IsingBulk.Anisotropic.NegativeNormalForm.Hessian
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Holomorphic removal of the actual separable-energy quotient, including
its derivative-defined value on the coordinate divisor. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

theorem analyticAt_dslope_center {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [hf.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hne
    exact (differentiableAt_dslope_of_ne hne).2 hz.differentiableAt
  · exact continuousAt_dslope_same.2 hf.differentiableAt

theorem derivative_dslope_relation {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    deriv (deriv f) a = 2 * deriv (dslope f a) a := by
  have hF := analyticAt_dslope_center hf
  have he : deriv f =ᶠ[𝓝 a] fun z => dslope f a z + (z-a) * deriv (dslope f a) z := by
    filter_upwards [hF.eventually_analyticAt] with z hz
    have hp := (((hasDerivAt_id z).sub_const a).mul hz.differentiableAt.hasDerivAt).add_const (f a)
    have hp' : HasDerivAt f (dslope f a z + (z-a)*deriv (dslope f a) z) z := by
      convert hp using 1
      · ext w
        simpa only [smul_eq_mul, sub_add_cancel, Pi.mul_apply, id_eq] using
          congrArg (fun x : ℂ => x + f a) (sub_smul_dslope f a w).symm
      · simp
    exact hp'.deriv
  have hd := hF.differentiableAt.hasDerivAt.add
    (((hasDerivAt_id a).sub_const a).mul hF.deriv.differentiableAt.hasDerivAt)
  have hh := hd.congr_of_eventuallyEq he
  simpa [two_mul] using hh.deriv

/-- Exact second divided difference, valid also at the double coincidence. -/
theorem energyQuotient_eq_double_dslope {f : ℂ → ℂ} {a h c : ℂ}
    (hf : AnalyticAt ℂ f a) (v : ℂ) :
    energyQuotient f (deriv f a) a h c v =
      -2 / (h*c) * dslope (dslope f a) a (a+v) := by
  by_cases hv : v = 0
  · subst v
    simp only [energyQuotient, ↓reduceIte, add_zero, dslope_same,
      derivative_dslope_relation hf]
    ring
  · have hav : a+v ≠ a := by simpa using hv
    simp only [energyQuotient, hv, ↓reduceIte, dslope_of_ne _ hav, dslope_same,
      slope_def_field, add_sub_cancel_left, energyRemainder]
    field_simp

theorem energyQuotient_analyticAt_zero {f : ℂ → ℂ} {a h c : ℂ}
    (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (energyQuotient f (deriv f a) a h c) 0 := by
  have hF := analyticAt_dslope_center (analyticAt_dslope_center hf)
  have hc : AnalyticAt ℂ (fun v : ℂ => dslope (dslope f a) a (a+v)) 0 := by
    apply hF.comp_of_eq (analyticAt_const.add analyticAt_id)
    simp
  have he : energyQuotient f (deriv f a) a h c =
      fun v => -2/(h*c) * dslope (dslope f a) a (a+v) :=
    funext (energyQuotient_eq_double_dslope hf)
  rw [he]
  exact analyticAt_const.mul hc

end
end IsingBulk.Anisotropic.NegativeNormalForm
