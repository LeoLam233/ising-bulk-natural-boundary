import IsingBulk.Tail.CompactRightPhaseTube
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-! Real jets of the analytic scalar phase model have exactly the complex
jet norms. This restricts the scalar field, not the real deformation bumps. -/
namespace IsingBulk.Tail
noncomputable section
open Set Metric
open scoped Topology

 theorem compactPhaseModel_real_jet_eq (p : ℂ × ℂ × ℂ)
    (hp : AnalyticAt ℂ compactPhaseModel p) (j : ℕ) :
    iteratedFDeriv ℝ j compactPhaseModel p=
      (iteratedFDeriv ℂ j compactPhaseModel p).restrictScalars ℝ :=
  ((hp.contDiffAt : ContDiffAt ℂ j compactPhaseModel p).restrictScalars_iteratedFDeriv (𝕜 := ℝ)).symm

 theorem compactPhaseModel_real_jet_difference_norm (p q : ℂ × ℂ × ℂ)
    (hp : AnalyticAt ℂ compactPhaseModel p) (hq : AnalyticAt ℂ compactPhaseModel q) (j : ℕ) :
    ‖iteratedFDeriv ℝ j compactPhaseModel p-iteratedFDeriv ℝ j compactPhaseModel q‖=
      ‖iteratedFDeriv ℂ j compactPhaseModel p-iteratedFDeriv ℂ j compactPhaseModel q‖ := by
  rw [compactPhaseModel_real_jet_eq p hp j,compactPhaseModel_real_jet_eq q hq j]
  rfl

 theorem compactPhaseModel_real_compact_tube {S a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |S-Real.cos θ|<1) (k : ℕ) :
    ∃ r B : ℝ, 0<r ∧ 0<B ∧ ∀ θ ∈ Icc a b, ∀ S' v : ℂ,
      max ‖S'-(S:ℂ)‖ ‖v‖≤r →
      AnalyticAt ℂ compactPhaseModel (S',v,(θ:ℂ)) ∧ ∀ j≤k,
      ‖iteratedFDeriv ℝ j compactPhaseModel (S',v,(θ:ℂ))‖≤B ∧
      ‖iteratedFDeriv ℝ j compactPhaseModel (S',v,(θ:ℂ))-
        iteratedFDeriv ℝ j compactPhaseModel ((S:ℂ),0,(θ:ℂ))‖≤B*max ‖S'-(S:ℂ)‖ ‖v‖ := by
  let K := (fun θ : ℝ => ((S:ℂ),(0:ℂ),(θ:ℂ))) '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hf : AnalyticOnNhd ℂ compactPhaseModel K := by
    rintro x ⟨θ,hθ,rfl⟩
    exact compactPhaseModel_analyticAt S θ (hmargin θ hθ)
  obtain ⟨ra,hra,hsub⟩ := hK.exists_cthickening_subset_open (isOpen_analyticAt ℂ compactPhaseModel) hf
  obtain ⟨rb,B,hrb,hB,hbounds⟩ := compactPhaseModel_compact_tube hmargin k
  refine ⟨min ra rb,B,lt_min hra hrb,hB,?_⟩
  intro θ hθ S' v hv
  have hnorm : ‖(S',v,(θ:ℂ))-((S:ℂ),0,(θ:ℂ))‖=max ‖S'-(S:ℂ)‖ ‖v‖ := by simp [Prod.norm_def]
  have hanalytic : AnalyticAt ℂ compactPhaseModel (S',v,(θ:ℂ)) :=
    hsub (mem_cthickening_of_dist_le _ ((S:ℂ),0,(θ:ℂ)) ra K ⟨θ,hθ,rfl⟩
      (by rw [dist_eq_norm,hnorm]; exact hv.trans (min_le_left _ _)))
  refine ⟨hanalytic,?_⟩
  intro j hj
  have hh := hbounds θ hθ S' v (hv.trans (min_le_right _ _)) j hj
  refine ⟨?_,?_⟩
  · rw [compactPhaseModel_real_jet_eq _ hanalytic j,ContinuousMultilinearMap.norm_restrictScalars]
    exact hh.1
  · rw [compactPhaseModel_real_jet_difference_norm _ _ hanalytic
      (compactPhaseModel_analyticAt S θ (hmargin θ hθ)) j]
    exact hh.2

end
end IsingBulk.Tail
