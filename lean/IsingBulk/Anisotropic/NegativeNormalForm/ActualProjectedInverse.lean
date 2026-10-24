import IsingBulk.Anisotropic.NegativeNormalForm.AnalyticSeparableMap
import IsingBulk.Anisotropic.NegativeNormalForm.ProjectedExtension

/-! The inverse below is constructed from the actual phase and implicit pole.
Its neighborhood is local; no dimension-uniform inverse radius is claimed here. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

theorem phaseSeparableMap_zero {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d t : ℂ) : phaseSeparableMap (n := n) B phi hphi d t 0=0 := by
  ext i
  simp [phaseSeparableMap,separableMap]

theorem exists_actual_projected_inverse {n : ℕ} (hn : n ≠ 0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0) (d : ℂ)
    (hB : AnalyticAt ℂ B (1-Complex.cos d)) (hBn : B (1-Complex.cos d) ≠ 0)
    (hh : centralHessian B phi d ≠ 0) :
    ∃ T : Config n → ℂ, ∃ V : Config n → Config n,
      AnalyticAt ℂ T 0 ∧ T 0=1-Complex.cos d ∧
      (∀ e : Equiv.Perm (Fin n), ∀ v, T (permute e v)=T v) ∧
      AnalyticAt ℂ V 0 ∧ V 0=0 ∧
      HasFDerivAt V (ContinuousLinearMap.id ℂ (Config n)) 0 ∧
      (∀ᶠ w in 𝓝 (0:Config n), ZeroMean w →
        ZeroMean (V w) ∧ project (phaseSeparableMap B phi hphi d (T (V w)) (V w))=w ∧
        poleEquation B phi hphi d (T (V w)) (V w)=0 ∧
        T (V w)-(1-Complex.cos d)=centralHessian B phi d/(2*n)*
          (quadratic w+n*mean (phaseSeparableMap B phi hphi d (T (V w)) (V w))^2)) := by
  obtain ⟨T,hT,hT0,hpole,hsym⟩ := exists_permutation_invariant_pole hn B phi hphi d hB hBn
  let U : Config n → Config n := fun v => phaseSeparableMap B phi hphi d (T v) v
  have hU := phaseSeparableMap_along_pole_analyticAt B phi hphi d hB hBn hh T hT hT0
  have hdU := phaseSeparableMap_along_pole_hasFDerivAt B phi hphi d hB hBn hh T hT hT0
  obtain ⟨V,hV,hV0,hdV,_hl,hr⟩ := exists_projected_inverse hn U hU
    (phaseSeparableMap_zero B phi hphi d (T 0)) hdU
  have ht : Filter.Tendsto V (𝓝 0) (𝓝 0) := by simpa [hV0] using hV.continuousAt.tendsto
  have hTV : Filter.Tendsto (fun w => T (V w)) (𝓝 0) (𝓝 (1-Complex.cos d)) := by
    simpa only [hT0,Function.comp_def] using hT.continuousAt.tendsto.comp ht
  have ha0 : phaseParameterQuotient B phi hphi d (1-Complex.cos d) ≠ 0 := by
    rw [phaseParameterQuotient_center B phi hphi d hB]
    exact centralParameterSlope_ne_zero B phi hphi d hBn
  have ha := (phaseParameterQuotient_analyticAt B phi hphi d hB).continuousAt.eventually_ne ha0
  refine ⟨T,V,hT,hT0,hsym,hV,hV0,hdV,?_⟩
  filter_upwards [hr,ht.eventually hpole,hTV.eventually ha] with w hw hp ha'
  intro hmean
  obtain ⟨hm,hproj⟩ := hw.2 hmean
  refine ⟨hm,hproj,hp,?_⟩
  rw [phaseSeparableMap_exact hn B phi hphi d (T (V w)) (V w) hm hh ha' hp]
  rw [← quadratic_project hn (U (V w)),hproj]

end
end IsingBulk.Anisotropic.NegativeNormalForm
