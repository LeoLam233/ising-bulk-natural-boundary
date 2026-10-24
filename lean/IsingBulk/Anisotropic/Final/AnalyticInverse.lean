import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.Basic

namespace IsingBulk.Anisotropic
noncomputable section
open Set Filter
open scoped Topology

/-- A local analytic inverse is constructed from the actual nonzero derivative,
not supplied as an unproved coordinate hypothesis. -/
theorem exists_analytic_local_inverse {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hd : deriv f z ≠ 0) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ (f z) ∧ ψ (f z) = z ∧
      (∀ᶠ w in 𝓝 (f z), f (ψ w) = w) ∧
      (∀ᶠ w in 𝓝 z, ψ (f w) = w) := by
  let i := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv f z) hd)
  have hfd : HasStrictFDerivAt f (i : ℂ →L[ℂ] ℂ) z :=
    hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hd
  let e := hfd.toOpenPartialHomeomorph f
  have hz : z ∈ e.source := hfd.mem_toOpenPartialHomeomorph_source
  have he : (e : ℂ → ℂ) = f := rfl
  have ha : AnalyticAt ℂ e.symm (f z) := by
    rw [← he]
    exact e.analyticAt_symm' hz (by simpa only [he] using hf)
      (by simpa only [he] using hfd.hasFDerivAt.fderiv)
  refine ⟨e.symm,ha,?_,?_,?_⟩
  · exact e.left_inv hz
  · exact e.eventually_right_inverse' hz
  · exact e.eventually_left_inverse hz

end
end IsingBulk.Anisotropic
