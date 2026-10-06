import IsingBulk.Tail.CompactPhaseAbsoluteJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric
open scoped Topology
attribute [local fun_prop] analyticAt_fst analyticAt_snd

def compactPhaseSourceModel (p : ℂ × ℂ × ℂ) : ℂ :=
  compactPhaseModel (sourceS p.1,p.2)

lemma compactPhaseSourceModel_analytic (s : ℂ) (hs : s ≠ 0) (v t : ℂ)
    (ha : AnalyticAt ℂ compactPhaseModel (sourceS s,v,t)) :
    AnalyticAt ℂ compactPhaseSourceModel (s,v,t) := by
  have hmap : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => (sourceS p.1,p.2)) (s,v,t) := by
    unfold sourceS
    exact (analyticAt_fst.add (analyticAt_fst.inv hs)).prod analyticAt_snd
  exact ha.comp (f := fun p : ℂ × ℂ × ℂ => (sourceS p.1,p.2)) hmap

/-- Uniform finite joint parameter and angular scalar jets, before composition
with the merely smooth, fully coupled real cutoff. -/
theorem compactPhaseSourceModel_compact_tube (d : LocalBranchData) {a b : ℝ}
    (hmargin : ∀ theta ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos theta|<1) (J : ℕ) :
    ∃ r B : ℝ, 0<r ∧ 0<B ∧ ∀ theta ∈ Icc a b, ∀ s v : ℂ,
      max ‖s-radialParameter d.theta 0‖ ‖v‖≤r →
      AnalyticAt ℂ compactPhaseSourceModel (s,v,(theta:ℂ)) ∧ ∀ j≤J,
      ‖iteratedFDeriv ℝ j compactPhaseSourceModel (s,v,(theta:ℂ))‖≤B := by
  let s0 := radialParameter d.theta 0
  let K := (fun theta : ℝ => (s0,(0:ℂ),(theta:ℂ))) '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hs : s0≠0 := norm_ne_zero_iff.mp (by simp [s0,radialParameter_norm])
  have hf : AnalyticOnNhd ℂ compactPhaseSourceModel K := by
    rintro x ⟨theta,ht,rfl⟩
    apply compactPhaseSourceModel_analytic s0 hs
    have he := sourceS_radial_zero_branch d
    simpa only [s0,he] using compactPhaseModel_analyticAt
      (1+Real.cos d.thetaB) theta (hmargin theta ht)
  obtain ⟨ra,hra,hsub⟩ := hK.exists_cthickening_subset_open
    (isOpen_analyticAt ℂ compactPhaseSourceModel) hf
  obtain ⟨rb,B,hrb,hB,hjets⟩ := compact_analytic_jet_bounds compactPhaseSourceModel hK hf J
  refine ⟨min ra rb,B,lt_min hra hrb,hB,?_⟩
  intro theta ht s v hv
  have hn : ‖(s,v,(theta:ℂ))-(s0,0,(theta:ℂ))‖=max ‖s-s0‖ ‖v‖ := by simp [Prod.norm_def]
  have ha : AnalyticAt ℂ compactPhaseSourceModel (s,v,(theta:ℂ)) :=
    hsub (mem_cthickening_of_dist_le _ (s0,0,(theta:ℂ)) ra K ⟨theta,ht,rfl⟩
      (by rw [dist_eq_norm,hn]; exact hv.trans (min_le_left _ _)))
  refine ⟨ha,?_⟩
  intro j hj
  have hh := (hjets (s0,0,(theta:ℂ)) ⟨theta,ht,rfl⟩ (s,v,(theta:ℂ))
    (by rw [hn]; exact hv.trans (min_le_right _ _)) j hj).1
  rw [← ((ha.contDiffAt : ContDiffAt ℂ j compactPhaseSourceModel _).restrictScalars_iteratedFDeriv (𝕜 := ℝ)),Function.comp_apply,ContinuousMultilinearMap.norm_restrictScalars]
  exact hh

end
end IsingBulk.Tail
