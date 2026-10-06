import IsingBulk.Tail.SelectedFCompactRootImage
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Absolute compact-root motion, as needed for actual Schur pair stability.
Only compact coordinates are moved when comparing with true branch roots. -/
namespace IsingBulk.Tail
noncomputable section
open Set Metric
open scoped Topology

 theorem continuedRoot_compact_motion {K : Set ℂ} (hK : IsCompact K)
    (hKD : K ⊆ continuedRootDomain) :
    ∃ c L : ℝ, 0 < c ∧ 0 < L ∧ ∀ W₀ ∈ K, ∀ W : ℂ,
      ‖W-W₀‖ ≤ c → W ∈ continuedRootDomain ∧
      ‖continuedRoot W-continuedRoot W₀‖ ≤ L*‖W-W₀‖ := by
  obtain ⟨r,hr,hsub⟩ := hK.exists_cthickening_subset_open continuedRootDomain_isOpen hKD
  obtain ⟨r',hr',hcompact⟩ := hK.exists_isCompact_cthickening
  let c := min r r'
  let K' := cthickening c K
  have hc : 0 < c := lt_min hr hr'
  have hK'D : K' ⊆ continuedRootDomain :=
    (cthickening_mono (min_le_left r r') K).trans hsub
  have hK' : IsCompact K' :=
    hcompact.of_isClosed_subset isClosed_cthickening (cthickening_mono (min_le_right r r') K)
  have hloc : LocallyLipschitzOn K' continuedRoot := by
    intro z hz
    have hdiff : ContDiffAt ℂ 1 continuedRoot z := (continuedRoot_analyticAt (hK'D hz)).contDiffAt
    obtain ⟨A,T,hT,hAT⟩ := hdiff.exists_lipschitzOnWith
    exact ⟨A,T,mem_nhdsWithin_of_mem_nhds hT,hAT⟩
  obtain ⟨A,hA⟩ := hloc.exists_lipschitzOnWith_of_compact hK'
  refine ⟨c,(A:ℝ)+1,hc,by positivity,?_⟩
  intro W₀ hW₀ W hW
  have hw₀ : W₀ ∈ K' := self_subset_cthickening K hW₀
  have hw : W ∈ K' := mem_cthickening_of_dist_le W W₀ c K hW₀ (by simpa only [dist_eq_norm] using hW)
  exact ⟨hK'D hw,(hA.norm_sub_le hw hw₀).trans
    (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))⟩

end
end IsingBulk.Tail
