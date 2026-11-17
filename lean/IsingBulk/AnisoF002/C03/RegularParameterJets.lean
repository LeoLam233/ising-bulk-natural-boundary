import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Generic joint analyticity of actual one-parameter derivatives

Repeated evaluation of the joint derivative at the parameter direction
is identified with the ordinary iterated derivative of every parameter
slice.  This supplies angular continuity and measurability for the actual
complete integrand jets used under the integral.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def parameterJet : ℕ → (ℂ × E → ℂ) → ℂ × E → ℂ
  | 0, f => f
  | n + 1, f => fun p => fderiv ℂ (parameterJet n f) p ((1 : ℂ), (0 : E))

theorem parameterJet_analyticAt {f : ℂ × E → ℂ} {p : ℂ × E}
    (hf : AnalyticAt ℂ f p) (n : ℕ) : AnalyticAt ℂ (parameterJet n f) p := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact ((ContinuousLinearMap.apply ℂ ℂ ((1 : ℂ), (0 : E))).analyticAt _).comp
      (f := fderiv ℂ (parameterJet n f)) ih.fderiv

theorem parameter_first_deriv_eq {f : ℂ × E → ℂ} {p : ℂ × E}
    (hf : AnalyticAt ℂ f p) :
    fderiv ℂ f p ((1 : ℂ), (0 : E)) = deriv (fun u : ℂ => f (u, p.2)) p.1 := by
  have hm : HasDerivAt (fun u : ℂ => (u, p.2)) ((1 : ℂ), (0 : E)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact (hf.differentiableAt.hasFDerivAt.comp_hasDerivAt p.1 hm).deriv.symm

theorem parameterJet_eq_iteratedDeriv {f : ℂ × E → ℂ} {p : ℂ × E}
    (hf : AnalyticAt ℂ f p) (n : ℕ) :
    parameterJet n f p = iteratedDeriv n (fun u : ℂ => f (u, p.2)) p.1 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have hm : ContinuousAt (fun u : ℂ => (u, p.2)) p.1 := by fun_prop
    have hnear : ∀ᶠ u : ℂ in 𝓝 p.1, AnalyticAt ℂ f (u, p.2) :=
      hm.eventually hf.eventually_analyticAt
    have he : (fun u : ℂ => parameterJet n f (u, p.2)) =ᶠ[𝓝 p.1]
        fun u => iteratedDeriv n (fun v : ℂ => f (v, p.2)) u :=
      hnear.mono fun u hu => ih hu
    change fderiv ℂ (parameterJet n f) p ((1 : ℂ), (0 : E)) = _
    rw [parameter_first_deriv_eq (parameterJet_analyticAt hf n), iteratedDeriv_succ]
    exact he.deriv_eq

/-- All fixed parameter derivatives remain jointly analytic in the full
complex parameter and auxiliary variables on the same local domain. -/
theorem parameterIteratedDeriv_analyticAt {f : ℂ × E → ℂ} {p : ℂ × E}
    (hf : AnalyticAt ℂ f p) (n : ℕ) :
    AnalyticAt ℂ (fun q : ℂ × E => iteratedDeriv n (fun u : ℂ => f (u, q.2)) q.1) p :=
  (parameterJet_analyticAt hf n).congr
    (hf.eventually_analyticAt.mono fun _ hq => parameterJet_eq_iteratedDeriv hq n)

end
end IsingBulk.AnisoF002.RegularTail.C03
