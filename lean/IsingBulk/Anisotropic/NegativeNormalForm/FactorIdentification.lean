import IsingBulk.Anisotropic.NegativeNormalForm.JointPhaseIdentity
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

/-- A genuine analytic factor determines the removable derivative value as well. -/
theorem dslope_eq_of_factorization {f A : ℂ → ℂ} {s : Set ℂ}
    (hs : s ∈ 𝓝 (0:ℂ)) (hA : AnalyticAt ℂ A 0)
    (he : ∀ v ∈ s, f v-f 0=v*A v) : ∀ v ∈ s, dslope f 0 v=A v := by
  have hEq : f =ᶠ[𝓝 (0:ℂ)] fun v => v*A v+f 0 := by
    filter_upwards [hs] with v hv
    linear_combination he v hv
  have hd := (((hasDerivAt_id (0:ℂ)).mul hA.differentiableAt.hasDerivAt).add_const (f 0)).congr_of_eventuallyEq hEq
  have hd0 : deriv f 0=A 0 := by simpa using hd.deriv
  intro v hv
  by_cases hv0 : v=0
  · simpa [hv0] using hd0
  · rw [dslope_of_ne _ hv0, slope_def_field]
    simp only [sub_zero]
    rw [he v hv]
    field_simp

theorem double_dslope_eq_of_factorization {f A H : ℂ → ℂ} {s : Set ℂ}
    (hs : s ∈ 𝓝 (0:ℂ)) (hA : AnalyticAt ℂ A 0) (hH : AnalyticAt ℂ H 0)
    (he : ∀ v ∈ s, f v-f 0=v*A v) (he' : ∀ v ∈ s, A v-A 0=v*H v) :
    ∀ v ∈ s, dslope (dslope f 0) 0 v=H v := by
  have hfirst := dslope_eq_of_factorization hs hA he
  have hsecond := dslope_eq_of_factorization hs hH he'
  have hEq : dslope f 0 =ᶠ[𝓝 (0:ℂ)] A := by
    filter_upwards [hs] with v hv using hfirst v hv
  intro v hv
  rw [← hsecond v hv]
  by_cases hv0 : v=0
  · simp only [hv0, dslope_same]
    exact hEq.deriv_eq
  · rw [dslope_of_ne _ hv0, dslope_of_ne _ hv0, slope_def_field, slope_def_field,
      hfirst v hv, hfirst 0 (mem_of_mem_nhds hs)]

theorem dslope_translate (f : ℂ → ℂ) (d v : ℂ) :
    dslope (fun u => f (d+u)) 0 v=dslope f d (d+v) := by
  by_cases hv : v=0
  · simp [hv, deriv_comp_const_add]
  · have hdv : d+v ≠ d := by simpa using hv
    simp [dslope_of_ne _ hv, dslope_of_ne _ hdv, slope_def_field]

theorem double_dslope_translate (f : ℂ → ℂ) (d v : ℂ) :
    dslope (dslope (fun u => f (d+u)) 0) 0 v=dslope (dslope f d) d (d+v) := by
  have he : dslope (fun u => f (d+u)) 0 = fun u => dslope f d (d+u) :=
    funext (dslope_translate f d)
  rw [he, dslope_translate]

end
end IsingBulk.Anisotropic.NegativeNormalForm
