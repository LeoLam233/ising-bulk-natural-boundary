import IsingBulk.Anisotropic.NegativeNormalForm.PoleEquation
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! An actual analytic implicit pole of the negative-edge phase equation.
This local existence theorem does not assert a dimension-uniform radius. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology ContDiff

/-- Joint holomorphy of the actual finite phase sum. -/
theorem poleEquation_analyticAt_center {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) :
    AnalyticAt ℂ (fun z : Config n × ℂ => poleEquation B phi hphi d z.2 z.1)
      (0, 1-Complex.cos d) := by
  apply Finset.analyticAt_fun_sum
  intro i _
  apply AnalyticAt.sub _ analyticAt_const
  have h := negativePhase_analyticAt_center B phi hphi d hB
  have hg : AnalyticAt ℂ (fun z : Config n × ℂ => (z.2, d+z.1 i))
      (0, 1-Complex.cos d) := by
    apply AnalyticAt.prod analyticAt_snd
    exact analyticAt_const.add (((ContinuousLinearMap.proj i : Config n →L[ℂ] ℂ).analyticAt _).comp
      (f := fun z : Config n × ℂ => z.1) analyticAt_fst)
  exact h.comp_of_eq hg (by simp)

/-- Existence and local uniqueness are proved from the phase equation's actual
nonzero t-derivative, rather than supplied as an abstract normal-form premise. -/
theorem exists_analytic_implicit_pole {n : ℕ} (hn : n ≠ 0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0) :
    ∃ T : Config n → ℂ,
      AnalyticAt ℂ T 0 ∧ T 0 = 1-Complex.cos d ∧
      (∀ᶠ v in 𝓝 (0 : Config n), poleEquation B phi hphi d (T v) v = 0) ∧
      (∀ᶠ z : Config n × ℂ in 𝓝 (0, 1-Complex.cos d),
        poleEquation B phi hphi d z.2 z.1 = 0 ↔ T z.1 = z.2) := by
  let F : Config n × ℂ → ℂ := fun z => poleEquation B phi hphi d z.2 z.1
  let u : Config n × ℂ := (0, 1-Complex.cos d)
  have hF : AnalyticAt ℂ F u := poleEquation_analyticAt_center B phi hphi d hB
  have hc : ContDiffAt ℂ ω F u := hF.contDiffAt
  let c : ℂ := n * (((Real.sin phi : ℂ)*Complex.I)⁻¹*B (1-Complex.cos d))
  have hcz : c ≠ 0 := poleEquation_parameter_derivative_ne_zero hn B phi hphi d hBn
  have hd := poleEquation_hasDerivAt_center (n := n) B phi hphi d (deriv B (1-Complex.cos d))
    hB.differentiableAt.hasDerivAt
  have hcomp := hF.differentiableAt.hasFDerivAt.comp (1-Complex.cos d)
    (ContinuousLinearMap.inr ℂ (Config n) ℂ).hasFDerivAt
  have he : fderiv ℂ F u ∘L ContinuousLinearMap.inr ℂ (Config n) ℂ =
      (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hcz)).toContinuousLinearMap := by
    exact hcomp.unique (hd.hasFDerivAt_equiv hcz)
  have hi : (fderiv ℂ F u ∘L ContinuousLinearMap.inr ℂ (Config n) ℂ).IsInvertible :=
    ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hcz), he.symm⟩
  refine ⟨hc.implicitFunction (by simp) hi,
    (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt,
    hc.implicitFunction_apply_self (by simp) hi, ?_, ?_⟩
  · simpa [F, u, poleEquation_center] using hc.eventually_apply_implicitFunction (by simp) hi
  · simpa [F, u, poleEquation_center] using hc.eventually_apply_eq_iff_implicitFunction (by simp) hi

end
end IsingBulk.Anisotropic.NegativeNormalForm
