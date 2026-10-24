import IsingBulk.Anisotropic.NegativeNormalForm.PermutationPole
import IsingBulk.Anisotropic.NegativeNormalForm.RemovableEnergy

/-! The actual separable map evaluated on the analytic implicit pole. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology BigOperators

def phaseParameterQuotient (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (d t : ℂ) : ℂ :=
  dslope (fun u => negativePhase B phi hphi u d) (1-Complex.cos d) t

theorem phaseParameterQuotient_identity (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) :
    negativePhase B phi hphi t d - (phi : ℂ)*Complex.I =
      phaseParameterQuotient B phi hphi d t * (t-(1-Complex.cos d)) := by
  simpa only [phaseParameterQuotient, smul_eq_mul, negativePhase_center, mul_comm] using
    (sub_smul_dslope (fun u => negativePhase B phi hphi u d) (1-Complex.cos d) t).symm

theorem phaseParameterQuotient_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d)) :
    AnalyticAt ℂ (phaseParameterQuotient B phi hphi d) (1-Complex.cos d) := by
  apply analyticAt_dslope_center
  exact (negativePhase_analyticAt_center B phi hphi d hB).comp
    (f := fun u : ℂ => (u,d)) (analyticAt_id.prod analyticAt_const)

theorem phaseParameterQuotient_center (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (hB : AnalyticAt ℂ B (1-Complex.cos d)) :
    phaseParameterQuotient B phi hphi d (1-Complex.cos d) =
      ((Real.sin phi : ℂ)*Complex.I)⁻¹*B (1-Complex.cos d) := by
  simpa only [phaseParameterQuotient, dslope_same] using (negativePhase_hasDerivAt_center B phi hphi d _ hB.differentiableAt.hasDerivAt).deriv

def phaseSeparableMap {n : ℕ} (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (d t : ℂ) (v : Config n) : Config n :=
  separableMap (negativePhase B phi hphi t) (deriv (negativePhase B phi hphi t) d)
    d (centralHessian B phi d) (phaseParameterQuotient B phi hphi d t) v

/-- Exact quadratic energy of the actual separable map, on the actual pole,
including all coordinate coincidences and the complex quadratic null cone. -/
theorem phaseSeparableMap_exact {n : ℕ} (hn : n ≠ 0) (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n) (hv : ZeroMean v)
    (hh : centralHessian B phi d ≠ 0) (ha : phaseParameterQuotient B phi hphi d t ≠ 0)
    (hpole : poleEquation B phi hphi d t v = 0) :
    t-(1-Complex.cos d) = centralHessian B phi d/(2*n) *
      quadratic (phaseSeparableMap B phi hphi d t v) := by
  rw [phaseSeparableMap, quadratic_separableMap]
  exact separable_energy_identity hn _ _ _ _ _ _ _ _ v hv hh ha
    (phaseParameterQuotient_identity B phi hphi d t) hpole

theorem phaseSeparableMap_permute {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) (v : Config n) (e : Equiv.Perm (Fin n)) :
    phaseSeparableMap B phi hphi d t (permute e v) =
      permute e (phaseSeparableMap B phi hphi d t v) := rfl

/-- Exact energy normal form for an actually constructed analytic pole and
separable map. Projection and mean correction remain distinct operations. -/
theorem exists_actual_separable_pole {n : ℕ} (hn : n ≠ 0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0)
    (hh : centralHessian B phi d ≠ 0) :
    ∃ T : Config n → ℂ,
      AnalyticAt ℂ T 0 ∧ T 0 = 1-Complex.cos d ∧
      (∀ e : Equiv.Perm (Fin n), ∀ v, T (permute e v) = T v) ∧
      (∀ᶠ v in 𝓝 (0 : Config n), ZeroMean v →
        T v-(1-Complex.cos d) = centralHessian B phi d/(2*n) *
          quadratic (phaseSeparableMap B phi hphi d (T v) v)) := by
  obtain ⟨T,hT,hT0,hsol,hsym⟩ := exists_permutation_invariant_pole hn B phi hphi d hB hBn
  have ha0 : phaseParameterQuotient B phi hphi d (1-Complex.cos d) ≠ 0 := by
    rw [phaseParameterQuotient_center B phi hphi d hB]
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero)) hBn
  have ha := (phaseParameterQuotient_analyticAt B phi hphi d hB).continuousAt.eventually_ne ha0
  have ht : Filter.Tendsto T (𝓝 0) (𝓝 (1-Complex.cos d)) := by simpa [hT0] using hT.continuousAt.tendsto
  refine ⟨T,hT,hT0,hsym,?_⟩
  filter_upwards [hsol, ht.eventually ha] with v hv hva
  intro hmean
  exact phaseSeparableMap_exact hn B phi hphi d (T v) v hmean hh hva hv

end
end IsingBulk.Anisotropic.NegativeNormalForm
