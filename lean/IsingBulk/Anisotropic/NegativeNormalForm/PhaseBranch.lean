import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-! Construction of the actual local inverse-cosh phase in ANISO (4.3).
Only the scalar noncritical condition is a premise. No anisotropic normal form,
residue estimate or analytic continuation is assumed. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

/-- A genuine analytic local inverse of cosh at every noncritical phase. -/
theorem exists_analytic_cosh_inverse (z : ℂ) (hz : Complex.sinh z ≠ 0) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (Complex.cosh z) ∧
      g (Complex.cosh z) = z ∧
      (∀ᶠ w in 𝓝 (Complex.cosh z), Complex.cosh (g w) = w) ∧
      HasDerivAt g (Complex.sinh z)⁻¹ (Complex.cosh z) := by
  have ha : AnalyticAt ℂ Complex.cosh z := Complex.analyticAt_cosh
  have hd : deriv Complex.cosh z ≠ 0 := by simpa using hz
  let g := ha.hasStrictDerivAt.localInverse Complex.cosh (deriv Complex.cosh z) z hd
  refine ⟨g, ha.analyticAt_localInverse hd, ?_, ?_, ?_⟩
  · exact HasStrictFDerivAt.localInverse_apply_image ..
  · exact HasStrictDerivAt.eventually_right_inverse ..
  · simpa only [Complex.deriv_cosh] using
      (HasStrictDerivAt.to_localInverse (hf := ha.hasStrictDerivAt) (hf' := hd)).hasDerivAt

/-- The inverse branch is centred at the selected imaginary physical phase,
not at a globally selected inverse-cosh branch. -/
theorem exists_edge_phase (phi : ℝ) (hphi : Real.sin phi ≠ 0) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (Real.cos phi : ℂ) ∧
      g (Real.cos phi : ℂ) = (phi : ℂ) * Complex.I ∧
      (∀ᶠ w in 𝓝 (Real.cos phi : ℂ), Complex.cosh (g w) = w) ∧
      HasDerivAt g ((Real.sin phi : ℂ) * Complex.I)⁻¹ (Real.cos phi : ℂ) := by
  have hs : Complex.sinh ((phi : ℂ) * Complex.I) ≠ 0 := by
    rw [Complex.sinh_mul_I]
    exact mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero
  simpa only [Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    using exists_analytic_cosh_inverse ((phi : ℂ) * Complex.I) hs

end
end IsingBulk.Anisotropic.NegativeNormalForm
