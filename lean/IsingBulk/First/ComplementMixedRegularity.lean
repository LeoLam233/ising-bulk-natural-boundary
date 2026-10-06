import IsingBulk.First.ComplementLocalParameterRegularity
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! Joint real smoothness of genuine complex parameter derivatives. -/
namespace IsingBulk.First
noncomputable section
open Filter
open scoped Topology ContDiff
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A holomorphic slice has the same derivative along the real direction 1. -/
theorem complex_deriv_eq_real_direction {f : ℂ → ℂ} {s : ℂ}
    (hf : DifferentiableAt ℂ f s) : deriv f s = phaseDirection (1 : ℂ) f s := by
  unfold phaseDirection
  rw [hf.fderiv_restrictScalars ℝ]
  rfl

/-- Ordinary joint real C∞ regularity and holomorphy of the parameter slices
imply joint real C∞ regularity of their actual complex derivative. -/
theorem contDiffAt_parameterized_complex_deriv {A : P × ℂ → ℂ} (p : P) (s : ℂ)
    (hA : ContDiffAt ℝ ∞ A (p,s))
    (hhol : ∀ᶠ q : P × ℂ in 𝓝 (p,s), DifferentiableAt ℂ (fun z => A (q.1,z)) q.2) :
    ContDiffAt ℝ ∞ (fun q : P × ℂ => deriv (fun z => A (q.1,z)) q.2) (p,s) := by
  apply (contDiffAt_parameterized_direction (1 : ℂ) p s hA).congr_of_eventuallyEq
  filter_upwards [hhol] with q hq
  exact complex_deriv_eq_real_direction hq

end
end IsingBulk.First
