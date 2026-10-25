import IsingBulk.Joint.Geometry.Definitions
import IsingBulk.Anisotropic.NegativeDominance.ContinuationRoots

/-! Canonical and negative-edge angular roots with two independent complex
couplings. The definitions do not pass through any fixed real ratio. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

def transferW (K : Coupling) (q : ℂ) : ℂ := (A K - T K * Complex.cos q) / S K

def transferRoot (K : Coupling) (q : ℂ) : ℂ := smallRoot (transferW K q)

def continuedTransferRoot (K : Coupling) (q : ℂ) : ℂ := continuedRoot (transferW K q)

theorem transferW_eq (K : Coupling) (q : ℂ) :
    transferW K q = transferC K - transferB K * Complex.cos q := by
  unfold transferW transferC transferB
  ring

theorem transferW_joint_analyticAt_of_S_ne_zero {K : Coupling} {q : ℂ}
    (hS : S K ≠ 0) :
    AnalyticAt ℂ (fun z : Coupling × ℂ => transferW z.1 z.2) (K,q) := by
  have hz : AnalyticAt ℂ (fun z : Coupling × ℂ => z.1.1) (K,q) :=
    analyticAt_fst.comp analyticAt_fst
  have hw : AnalyticAt ℂ (fun z : Coupling × ℂ => z.1.2) (K,q) :=
    analyticAt_snd.comp analyticAt_fst
  have hq : AnalyticAt ℂ (fun z : Coupling × ℂ => z.2) (K,q) := analyticAt_snd
  exact (((Complex.analyticAt_cosh.comp hz).mul (Complex.analyticAt_cosh.comp hw)).sub
    ((Complex.analyticAt_sinh.comp hw).mul (Complex.analyticAt_cos.comp hq))).div
    (Complex.analyticAt_sinh.comp hz) hS

theorem transferW_mem_smallRootDomain {K : Coupling}
    (hK : K ∉ spectralSet) (hS : S K ≠ 0) (q : ℝ) :
    transferW K (q : ℂ) ∈ SmallRootDomain := by
  by_contra hh
  simp only [SmallRootDomain,mem_ofPred_eq,not_or,not_ne_iff,not_lt] at hh
  have he : transferW K (q : ℂ) = ((transferW K (q : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [hh.1]
  apply hK
  refine ⟨(transferW K (q : ℂ)).re, ⟨hh.2.2,hh.2.1⟩, Real.cos q,
    ⟨Real.neg_one_le_cos q, Real.cos_le_one q⟩, ?_⟩
  unfold transferW at he
  rw [← Complex.ofReal_cos] at he
  have hm := (div_eq_iff hS).mp he
  unfold transferW
  rw [← Complex.ofReal_cos]
  linear_combination hm

theorem transferRoot_bounds {K : Coupling} (hK : K ∉ spectralSet)
    (hS : S K ≠ 0) (q : ℝ) : transferRoot K (q : ℂ) ≠ 0 ∧ ‖transferRoot K (q : ℂ)‖ < 1 :=
  ⟨smallRoot_ne_zero (transferW_mem_smallRootDomain hK hS q),
    (smallRoot_spec (transferW_mem_smallRootDomain hK hS q)).2⟩

theorem transferRoot_joint_analyticAt {K : Coupling} (hK : K ∉ spectralSet)
    (hS : S K ≠ 0) (q : ℝ) :
    AnalyticAt ℂ (fun z : Coupling × ℂ => transferRoot z.1 z.2) (K,(q : ℂ)) :=
  AnalyticAt.fun_comp_of_eq
    (f := fun z : Coupling × ℂ => transferW z.1 z.2) (g := smallRoot)
    (smallRoot_analyticAt (transferW_mem_smallRootDomain hK hS q))
    (transferW_joint_analyticAt_of_S_ne_zero hS) rfl

theorem negative_transferW_eq_edgeW {b : ℝ} {K : Coupling} (hS : S K ≠ 0)
    (hedge : A K + T K = (b : ℂ) * S K) (q : ℝ) :
    transferW K (q : ℂ) = edgeW b (-T K / S K) (q - Real.pi) := by
  unfold transferW edgeW
  rw [← Complex.ofReal_cos, Real.cos_sub_pi]
  push_cast
  field_simp [hS]
  linear_combination hedge

theorem continuedTransferRoot_eq_edgeRoot {b : ℝ} {K : Coupling} (hS : S K ≠ 0)
    (hedge : A K + T K = (b : ℂ) * S K) (q : ℝ) :
    continuedTransferRoot K (q : ℂ) = edgeRoot b (-T K / S K) (q - Real.pi) := by
  unfold continuedTransferRoot edgeRoot
  rw [negative_transferW_eq_edgeW hS hedge]

theorem continuedTransferRoot_negative_joint_analyticAt {b : ℝ} {K : Coupling}
    (hS : S K ≠ 0) (hedge : A K + T K = (b : ℂ) * S K)
    (hb : |b| < 1) (hB : 0 < (-T K / S K).im) (q : ℝ) :
    AnalyticAt ℂ (fun z : Coupling × ℂ => continuedTransferRoot z.1 z.2) (K,(q : ℂ)) := by
  have hW : transferW K (q : ℂ) ∈ continuedRootDomain := by
    rw [negative_transferW_eq_edgeW hS hedge]
    exact edgeW_domain hb hB _
  exact AnalyticAt.fun_comp_of_eq
    (f := fun z : Coupling × ℂ => transferW z.1 z.2) (g := continuedRoot)
    (continuedRoot_analyticAt hW) (transferW_joint_analyticAt_of_S_ne_zero hS) rfl

theorem continuedTransferRoot_negative_pair_ne_zero {b : ℝ} {K : Coupling}
    (hS : S K ≠ 0) (hedge : A K + T K = (b : ℂ) * S K)
    (hb : |b| < 1) (hB : 0 < (-T K / S K).im) (q t : ℝ) :
    1 - continuedTransferRoot K (q : ℂ) * continuedTransferRoot K (t : ℂ) ≠ 0 := by
  rw [continuedTransferRoot_eq_edgeRoot hS hedge, continuedTransferRoot_eq_edgeRoot hS hedge]
  exact edgeRoot_pair_denominator_ne_zero hb hB _ _

theorem continuedTransferRoot_odd_negative_product_lt_one {N : ℕ} (hN : Odd N)
    {b : ℝ} {K : Coupling} (hS : S K ≠ 0) (hedge : A K + T K = (b : ℂ) * S K)
    (hb : |b| < 1) (hB : 0 < (-T K / S K).im)
    (q : Fin N → ℝ) (hq : ∑ i, q i = 0) :
    ‖∏ i, continuedTransferRoot K (q i : ℂ)‖ < 1 := by
  simp_rw [continuedTransferRoot_eq_edgeRoot hS hedge]
  exact odd_negative_root_product_lt_one hN hb hB q hq

theorem continuedTransferRoot_eq_transferRoot_of_im_pos {K : Coupling} {q : ℂ}
    (hi : 0 < (transferW K q).im) : continuedTransferRoot K q = transferRoot K q := by
  unfold continuedTransferRoot transferRoot
  rw [continuedRoot_eq_interiorRoot hi]
  exact (smallRoot_eq_of_quadratic (Or.inl (ne_of_gt hi))
    (interiorRoot_quadratic _) (interiorRoot_norm_lt_one hi)).symm

end
end IsingBulk.Joint.Negative
