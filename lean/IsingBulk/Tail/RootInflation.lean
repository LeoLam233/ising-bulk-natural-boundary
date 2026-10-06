import IsingBulk.Tail.CompactRootContinuation
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.MetricSpace.Thickening

/-! Uniform multiplicative inflation of the actual continued root on compact
regular pieces. Constants are chosen once for the compact root cover, before
particle count or any parameter disk is chosen. -/
namespace IsingBulk.Tail
noncomputable section
open Set Metric
open scoped Topology BigOperators

theorem continuedRoot_compact_inflation {K : Set ℂ} (hK : IsCompact K)
    (hKD : K ⊆ continuedRootDomain) :
    ∃ c L : ℝ, 0 < c ∧ 0 < L ∧ ∀ W₀ ∈ K, ∀ W : ℂ,
      ‖W-W₀‖ ≤ c → W ∈ continuedRootDomain ∧
      ‖continuedRoot W‖ ≤ ‖continuedRoot W₀‖*Real.exp (L*‖W-W₀‖) := by
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
  have hinv : ContinuousOn (fun z : ℂ => (continuedRoot z)⁻¹) K' := by
    intro z hz
    exact ((continuedRoot_analyticAt (hK'D hz)).continuousAt.inv₀
      (continuedRoot_nonzero z)).continuousWithinAt
  obtain ⟨M,hM⟩ := hK'.exists_bound_of_continuousOn hinv
  let B := max M 0+1
  have hB : 0 < B := by dsimp [B]; have := le_max_right M 0; linarith
  let L := (A:ℝ)*B+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨c,L,hc,hL,?_⟩
  intro W₀ hW₀ W hW
  have hw₀ : W₀ ∈ K' := self_subset_cthickening K hW₀
  have hw : W ∈ K' := mem_cthickening_of_dist_le W W₀ c K hW₀ (by simpa [dist_eq_norm] using hW)
  refine ⟨hK'D hw,?_⟩
  have hlip : ‖continuedRoot W-continuedRoot W₀‖ ≤ (A:ℝ)*‖W-W₀‖ :=
    hA.norm_sub_le hw hw₀
  have hnorm : 0 < ‖continuedRoot W₀‖ := norm_pos_iff.mpr (continuedRoot_nonzero W₀)
  have hmin : 1 ≤ B*‖continuedRoot W₀‖ := by
    have hin := hM W₀ hw₀
    rw [norm_inv] at hin
    have hin' : ‖continuedRoot W₀‖⁻¹ ≤ B := by
      dsimp [B]
      have := le_max_left M 0
      linarith
    have hh := mul_le_mul_of_nonneg_right hin' hnorm.le
    rwa [inv_mul_cancel₀ hnorm.ne'] at hh
  have hlinear : ‖continuedRoot W‖ ≤ ‖continuedRoot W₀‖*(1+L*‖W-W₀‖) := by
    have hnormdiff := norm_sub_norm_le (continuedRoot W) (continuedRoot W₀)
    have hscaled := mul_le_mul_of_nonneg_right hmin
      (show 0 ≤ (A:ℝ)*‖W-W₀‖ by positivity)
    dsimp [L]
    nlinarith [mul_nonneg hnorm.le (norm_nonneg (W-W₀))]
  exact hlinear.trans (mul_le_mul_of_nonneg_left
    (by simpa [add_comm] using Real.add_one_le_exp (L*‖W-W₀‖)) hnorm.le)

/-- A named contracting root absorbs the inflation of every compact root.
This is an exact dimension count, valid before any N-window restriction. -/
theorem finite_product_anchor_inflation {N : ℕ} (z : Fin N → ℂ) (q : Fin N)
    (a L d : ℝ) (hall : ∀ i, ‖z i‖ ≤ Real.exp (L*d))
    (hq : ‖z q‖ ≤ Real.exp (-a+L*d)) :
    ‖∏ i, z i‖ ≤ Real.exp (-a+(N:ℝ)*L*d) := by
  calc
    _ = ∏ i, ‖z i‖ := norm_prod _ _
    _ ≤ ∏ i : Fin N, Real.exp ((if i=q then -a else 0)+L*d) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      by_cases hi : i=q
      · simpa [hi] using hq
      · simpa [hi] using hall i
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

/-- Source-root product bound on a compact/true-branch cover. The compact
cover condition remains visible until the fixed support construction supplies
it; it is not replaced by an assumed product-gap estimate. -/
theorem continuedRoot_compact_branch_product {K : Set ℂ} (hK : IsCompact K)
    (hKD : K ⊆ continuedRootDomain) :
    ∃ c L : ℝ, 0 < c ∧ 0 < L ∧ ∀ (N : ℕ) (W₀ W : Fin N → ℂ) (q : Fin N)
      (a d : ℝ), 0 ≤ d → d ≤ c →
      (∀ i, 0 < (W₀ i).im) →
      (∀ i, W₀ i ∈ K ∨ 0 < (W i).im) →
      (∀ i, ‖W i-W₀ i‖ ≤ d) → W₀ q ∈ K →
      ‖continuedRoot (W₀ q)‖ ≤ Real.exp (-a) →
      (∀ i, W i ∈ continuedRootDomain) ∧
      ‖∏ i, continuedRoot (W i)‖ ≤ Real.exp (-a+(N:ℝ)*L*d) := by
  obtain ⟨c,L,hc,hL,hinflate⟩ := continuedRoot_compact_inflation hK hKD
  refine ⟨c,L,hc,hL,?_⟩
  intro N W₀ W q a d hd hdc hcenter hcover hdiff hqK hq
  have hroot (i) : W i ∈ continuedRootDomain ∧
      ‖continuedRoot (W i)‖ ≤ Real.exp (L*d) := by
    rcases hcover i with hk | hu
    · obtain ⟨hdom,hb⟩ := hinflate (W₀ i) hk (W i) ((hdiff i).trans hdc)
      have hbase : ‖continuedRoot (W₀ i)‖ ≤ 1 := by
        rw [continuedRoot_eq_interiorRoot (hcenter i)]
        exact (IsingBulk.First.interiorRoot_norm_lt_one (hcenter i)).le
      refine ⟨hdom,hb.trans ?_⟩
      calc
        _ ≤ Real.exp (L*‖W i-W₀ i‖) := mul_le_of_le_one_left (Real.exp_pos _).le hbase
        _ ≤ Real.exp (L*d) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hdiff i) hL.le)
    · refine ⟨Or.inl (Or.inl hu),?_⟩
      rw [continuedRoot_eq_interiorRoot hu]
      exact (IsingBulk.First.interiorRoot_norm_lt_one hu).le.trans
        (Real.one_le_exp_iff.mpr (mul_nonneg hL.le hd))
  refine ⟨fun i => (hroot i).1,?_⟩
  apply finite_product_anchor_inflation (fun i => continuedRoot (W i)) q a L d (fun i => (hroot i).2)
  have hb := (hinflate (W₀ q) hqK (W q) ((hdiff q).trans hdc)).2
  calc
    _ ≤ ‖continuedRoot (W₀ q)‖*Real.exp (L*‖W q-W₀ q‖) := hb
    _ ≤ Real.exp (-a)*Real.exp (L*d) :=
      mul_le_mul hq (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hdiff q) hL.le))
        (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end
end IsingBulk.Tail
