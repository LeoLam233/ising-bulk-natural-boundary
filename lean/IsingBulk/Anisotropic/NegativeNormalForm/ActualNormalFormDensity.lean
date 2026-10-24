import IsingBulk.Anisotropic.NegativeNormalForm.EquivariantLocalNormalForm
import IsingBulk.Anisotropic.NegativeNormalForm.FullTransformedDensity

/-! The actual local normal form with its complete analytic density.
This theorem does not assert a dimension-uniform neighborhood or error bound. -/
noncomputable section
open Filter
open scoped Topology
namespace IsingBulk.Anisotropic.NegativeNormalForm

 theorem exists_actual_normal_form_with_full_density (m : ℕ)
    (B rootB : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0)
    (hr : AnalyticAt ℂ rootB (1-Complex.cos d)) (hrn : rootB (1-Complex.cos d) ≠ 0)
    (hh : centralHessian B phi d ≠ 0) :
    ∃ T : Config (m+1) → ℂ, ∃ Phi : Config (m+1) → Config (m+1),
      AnalyticAt ℂ T 0 ∧ T 0=1-Complex.cos d ∧
      AnalyticAt ℂ Phi 0 ∧ Phi 0=0 ∧
      HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config (m+1))) 0 ∧
      (∀ e : Equiv.Perm (Fin (m+1)), ∀ v, Phi (permute e v)=permute e (Phi v)) ∧
      AnalyticAt ℂ (normalizedFullDensity B rootB phi hphi d T Phi) 0 ∧
      normalizedFullDensity B rootB phi hphi d T Phi 0=1 ∧
      (∀ᶠ u in 𝓝 (0 : Config m),
        ZeroMean (Phi (freeChartCLM m u)) ∧
        poleEquation B phi hphi d (T (Phi (freeChartCLM m u))) (Phi (freeChartCLM m u))=0 ∧
        T (Phi (freeChartCLM m u))=1-Complex.cos d+
          centralHessian B phi d/(2*(m+1))*quadratic (freeChartCLM m u) ∧
        poleResidue B rootB phi hphi d T (Phi (freeChartCLM m u))*constrainedJacobian Phi u =
          vandermonde (freeChartCLM m u)^2 * regularResidue B rootB phi hphi d T 0 *
            normalizedFullDensity B rootB phi hphi d T Phi u) := by
  obtain ⟨T,Phi,hT,hT0,_hTsym,hPhi,hPhi0,hd,hsym,hactual⟩ :=
    exists_equivariant_actual_local_normal_form (Nat.succ_ne_zero m) B phi hphi d hB hBn hh
  have ha := normalizedFullDensity_analyticAt B rootB phi hphi d hB hBn hr hrn T hT hT0 Phi hPhi hPhi0
  have hzero := normalizedFullDensity_zero B rootB phi hphi d hB hBn hr hrn T hT hT0 Phi hPhi0 hd
  have hR : regularResidue B rootB phi hphi d T 0 ≠ 0 :=
    (regularResidue_eventually_ne_zero (Nat.succ_ne_zero m) B rootB phi hphi d hB hBn hr hrn T hT hT0).self_of_nhds
  have ht : Tendsto (freeChartCLM m) (𝓝 0) (𝓝 0) := by
    simpa using ((freeChartCLM m).continuous.continuousAt (x := 0)).tendsto
  refine ⟨T,Phi,hT,hT0,hPhi,hPhi0,hd,hsym,ha,hzero,?_⟩
  filter_upwards [ht.eventually hactual,poleResidue_full_pullback B rootB phi hphi d T Phi hPhi hsym] with u hu hp
  obtain ⟨hm,he,hq⟩ := hu (freeChartCLM_zeroMean m u)
  refine ⟨hm,he,?_,?_⟩
  · convert hq using 1
    push_cast
    ring
  · rw [hp]
    unfold normalizedFullDensity
    field_simp [hR]

end IsingBulk.Anisotropic.NegativeNormalForm
