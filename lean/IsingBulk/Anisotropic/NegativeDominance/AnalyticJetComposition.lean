import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set

/-- Local scalar composition bound for changing the nonramified edge
coordinate. Only finitely many outer jets enter each fixed order. -/
theorem analytic_jet_comp_norm_bound {f g : ℂ → ℂ} {V U : Set ℂ}
    (hV : IsOpen V) (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f V)
    (hg : AnalyticOnNhd ℂ g U) (hmap : MapsTo f V U)
    {x : ℂ} (hx : x∈V) (j : ℕ) {C D : ℝ}
    (hC : ∀ i, i≤j → ‖iteratedDeriv i g (f x)‖≤C)
    (hD : ∀ i : ℕ, 1 ≤ i → i ≤ j → ‖iteratedDeriv i f x‖≤D^i) :
    ‖iteratedDeriv j (fun y => g (f y)) x‖≤(j.factorial : ℝ)*C*D^j := by
  have hh := norm_iteratedFDerivWithin_comp_le
    (𝕜 := ℂ) (n := j) (N := j)
    (hg.contDiffOn hU.uniqueDiffOn) (hf.contDiffOn hV.uniqueDiffOn) le_rfl
    hU.uniqueDiffOn hV.uniqueDiffOn hmap hx
    (C := C) (D := D) ?_ ?_
  · simpa only [iteratedFDerivWithin_of_isOpen j hV hx,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv,Function.comp_def] using hh
  · intro i hi
    rw [iteratedFDerivWithin_of_isOpen i hU (hmap hx),
      norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC i hi
  · intro i hi hj
    rw [iteratedFDerivWithin_of_isOpen i hV hx,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hD i hi hj

end
end IsingBulk.Anisotropic.NegativeDominance
