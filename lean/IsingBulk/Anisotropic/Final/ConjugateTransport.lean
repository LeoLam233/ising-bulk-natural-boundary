import IsingBulk.Anisotropic.Final.LocalExtension
import IsingBulk.Anisotropic.Final.RealIntervalUniqueness
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral

namespace IsingBulk.Anisotropic
noncomputable section
open Set Filter
open scoped Topology

theorem analyticAt_conjugate_reflection {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f (star z)) : AnalyticAt ℂ (fun w => star (f (star w))) z := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hc : ContinuousAt (star : ℂ → ℂ) z := continuous_star.continuousAt
  filter_upwards [hc.tendsto.eventually hf.eventually_analyticAt] with w hw
  simpa only [Function.comp_def,Complex.star_def,starRingEnd_self_apply] using hw.differentiableAt.star_conj

theorem domain_extension_conjugate_pullback {D : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (he : HasDomainExtension D f (star z)) :
    HasDomainExtension (star ⁻¹' D) (fun w => star (f (star w))) z := by
  obtain ⟨U,hU,hz,g,hg,hEq⟩ := he
  refine ⟨star ⁻¹' U,hU.preimage continuous_star,hz,fun w => star (g (star w)),?_,?_⟩
  · intro w hw
    exact analyticAt_conjugate_reflection (hg (star w) hw)
  · intro w hw
    exact congrArg star (hEq ⟨hw.1,hw.2⟩)

theorem domain_extension_of_conjugate {D : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hD : ∀ w, star w∈D ↔ w∈D) (hf : ∀ w∈D, star (f (star w))=f w)
    (he : HasDomainExtension D f (star z)) : HasDomainExtension D f z := by
  have hh := domain_extension_conjugate_pullback he
  have hset : star ⁻¹' D=D := Set.ext hD
  rw [hset] at hh
  exact domain_extension_of_eqOn (fun w hw => (hf w hw).symm) hh

theorem reflection_eqOn_of_real_interval {D : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f D) (hconn : IsPreconnected D)
    (hD : ∀ w, star w∈D ↔ w∈D) {a b : ℝ} (hab : a<b)
    (hi : ∀ x∈Ioo a b, (x:ℂ)∈D)
    (hreal : ∀ x∈Ioo a b, star (f (x:ℂ))=f (x:ℂ)) :
    EqOn (fun w => star (f (star w))) f D := by
  apply analytic_eqOn_of_real_interval
    (fun w hw => analyticAt_conjugate_reflection (hf (star w) ((hD w).mpr hw)))
    hf hconn hab hi
  intro x hx
  simpa only [Complex.star_def,Complex.conj_ofReal] using hreal x hx

end
end IsingBulk.Anisotropic
