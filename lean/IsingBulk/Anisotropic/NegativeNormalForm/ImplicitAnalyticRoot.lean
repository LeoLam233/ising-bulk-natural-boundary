import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem exists_analytic_scalar_root {F : E × ℂ → ℂ} {v : E} {t : ℂ}
    (hF : AnalyticAt ℂ F (v,t)) (hz : F (v,t)=0)
    (hd : deriv (fun s => F (v,s)) t≠0) :
    ∃ g : E → ℂ, AnalyticAt ℂ g v ∧ g v=t ∧ ∀ᶠ w in 𝓝 v, F (w,g w)=0 := by
  have hc : ContDiffAt ℂ ω F (v,t) := hF.contDiffAt
  have hin : HasFDerivAt (fun s : ℂ => (v,s)) (ContinuousLinearMap.inr ℂ E ℂ) t := by
    simpa using ((ContinuousLinearMap.inr ℂ E ℂ).hasFDerivAt (x := t)).const_add (v,0)
  have hcomp := hF.differentiableAt.hasFDerivAt.comp t hin
  have hpart := (hF.fun_comp_of_eq (f := fun s : ℂ => (v,s))
    (analyticAt_const.prod analyticAt_id) rfl).differentiableAt.hasDerivAt
  let c := deriv (fun s => F (v,s)) t
  have he : fderiv ℂ F (v,t) ∘L ContinuousLinearMap.inr ℂ E ℂ=
      (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hd)).toContinuousLinearMap :=
    hcomp.unique (hpart.hasFDerivAt_equiv hd)
  have hi : (fderiv ℂ F (v,t) ∘L ContinuousLinearMap.inr ℂ E ℂ).IsInvertible :=
    ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hd),he.symm⟩
  refine ⟨hc.implicitFunction (by simp) hi,
    (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt,
    hc.implicitFunction_apply_self (by simp) hi,?_⟩
  simpa only [hz] using hc.eventually_apply_implicitFunction (by simp) hi

theorem analyticOnNhd_of_unique_scalar_roots {F : E × ℂ → ℂ} {T : E → ℂ}
    {U : Set E} (hU : IsOpen U) (a : ℂ) (R : ℝ)
    (hroot : ∀ v∈U, F (v,T v)=0)
    (ha : ∀ v∈U, AnalyticAt ℂ F (v,T v))
    (hd : ∀ v∈U, deriv (fun s => F (v,s)) (T v)≠0)
    (hb : ∀ v∈U, ‖T v-a‖<R)
    (hu : ∀ v∈U, ∀ s∈closedBall a R, F (v,s)=0 → s=T v) :
    AnalyticOnNhd ℂ T U := by
  intro v hv
  obtain ⟨g,hg,hgv,hgz⟩ := exists_analytic_scalar_root (ha v hv) (hroot v hv) (hd v hv)
  have hsmall : ∀ᶠ w in 𝓝 v, ‖g w-a‖<R :=
    (hg.continuousAt.sub continuousAt_const).norm.eventually_lt continuousAt_const
      (by simpa only [Pi.sub_apply,hgv] using hb v hv)
  apply hg.congr
  filter_upwards [hU.mem_nhds hv,hgz,hsmall] with w hw hz hsmall
  exact hu w hw (g w) (by simpa only [mem_closedBall,dist_eq_norm] using hsmall.le) hz

end
end IsingBulk.Anisotropic.NegativeNormalForm
