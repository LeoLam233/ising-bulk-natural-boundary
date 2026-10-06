import IsingBulk.Tail.CompactGuardRealJets
import IsingBulk.Tail.AllBranchExteriorTruncationLimit

namespace IsingBulk.Tail
noncomputable section
open Set Filter Function
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000

theorem compactPairWeightDenom_smooth {N : ℕ} (P : Finset (Fin N × Fin N)) (M : ℕ) :
    ContDiff ℝ ∞ (compactPairWeightDenom P M) := by
  unfold compactPairWeightDenom
  fun_prop

theorem compactPairWeightDenom_selected_pos {N : ℕ} (P : Finset (Fin N × Fin N))
    (M : ℕ) {i j : Fin N} (hij : (i,j) ∈ P) {θ : Fin N → ℝ} (hθ : θ i ≠ θ j) :
    0 < compactPairWeightDenom P M θ :=
  (pow_pos (abs_pos.mpr (sub_ne_zero.mpr hθ)) (2*M)).trans_le
    (compactPairWeightDenom_lower P M θ _ ⟨(i,j),hij,rfl⟩)

theorem compactPairWeight_range {N : ℕ} (P : Finset (Fin N × Fin N)) (M : ℕ)
    {i j : Fin N} (hij : (i,j) ∈ P) (θ : Fin N → ℝ) :
    0 ≤ compactPairWeight P M i j θ ∧ compactPairWeight P M i j θ ≤ 1 := by
  have hn : 0 ≤ (θ i-θ j)^(2*M) := by rw [pow_mul]; positivity
  have hd := compactPairWeightDenom_nonneg P M θ
  refine ⟨div_nonneg hn hd,?_⟩
  by_cases hz : compactPairWeightDenom P M θ=0
  · simp [compactPairWeight,hz]
  · apply (div_le_one (lt_of_le_of_ne hd (Ne.symm hz))).mpr
    simpa only [pow_mul,sq_abs] using compactPairWeightDenom_lower P M θ _ ⟨(i,j),hij,rfl⟩

theorem compactPairWeight_measurable {N : ℕ} (P : Finset (Fin N × Fin N)) (M : ℕ) (i j : Fin N) :
    Measurable (compactPairWeight P M i j) := by
  exact (((measurable_pi_apply i).sub (measurable_pi_apply j)).pow_const _).div
    (compactPairWeightDenom_smooth P M).continuous.measurable

def compactGuardedPairWeight {N : ℕ} (P : Finset (Fin N × Fin N)) (M : ℕ)
    (h : ℝ) (i j : Fin N) (θ : Fin N → ℝ) : ℝ :=
  compactPairWeight P M i j θ*allBranchSelectedGuard h i j θ

theorem compactGuardedPairWeight_support {N : ℕ} (P : Finset (Fin N × Fin N))
    (M : ℕ) {h : ℝ} (hh : 0 < h) (i j : Fin N) :
    tsupport (compactGuardedPairWeight P M h i j) ⊆ {θ | h/2 ≤ |θ i-θ j|} :=
  tsupport_mul_subset_right.trans (allBranchSelectedGuard_tsupport hh i j)

theorem compactGuardedPairWeight_smooth {N : ℕ} (P : Finset (Fin N × Fin N))
    (M : ℕ) {h : ℝ} (hh : 0 < h) {i j : Fin N} (hij : (i,j) ∈ P) :
    ContDiff ℝ ∞ (compactGuardedPairWeight P M h i j) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  by_cases hθ : θ ∈ tsupport (allBranchSelectedGuard h i j)
  · have hgap : 0 < |θ i-θ j| := (half_pos hh).trans_le (allBranchSelectedGuard_tsupport hh i j hθ)
    have hd := compactPairWeightDenom_selected_pos P M hij (sub_ne_zero.mp (abs_pos.mp hgap))
    have hnum : ContDiff ℝ ∞ (fun x : Fin N → ℝ => (x i-x j)^(2*M)) := by fun_prop
    exact (hnum.contDiffAt.div (compactPairWeightDenom_smooth P M).contDiffAt hd.ne').mul
      (allBranchSelectedGuard_smooth h i j).contDiffAt
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hθ] with x hx
    change compactPairWeight P M i j x*allBranchSelectedGuard h i j x=0
    rw [show allBranchSelectedGuard h i j x=0 from hx,mul_zero]

theorem compactGuardedPairWeight_range {N : ℕ} (P : Finset (Fin N × Fin N))
    (M : ℕ) (h : ℝ) {i j : Fin N} (hij : (i,j) ∈ P) (θ : Fin N → ℝ) :
    0 ≤ compactGuardedPairWeight P M h i j θ ∧ compactGuardedPairWeight P M h i j θ ≤ 1 := by
  have hw := compactPairWeight_range P M hij θ
  have hg := allBranchSelectedGuard_range h i j θ
  refine ⟨mul_nonneg hw.1 hg.1,?_⟩
  simpa only [compactGuardedPairWeight,one_mul] using
    mul_le_mul hw.2 hg.2 hg.1 (by norm_num : (0:ℝ) ≤ 1)

theorem compactGuardedPairWeight_eventually {N : ℕ} (P : Finset (Fin N × Fin N))
    (M : ℕ) (i j : Fin N) (θ : Fin N → ℝ) (hθ : θ i ≠ θ j) :
    ∀ᶠ k in atTop, compactGuardedPairWeight P M (allBranchTruncationScale k) i j θ=
      compactPairWeight P M i j θ := by
  have hgap : 0 < |θ i-θ j| := abs_pos.mpr (sub_ne_zero.mpr hθ)
  filter_upwards [allBranchTruncationScale_tendsto.eventually (gt_mem_nhds hgap)] with k hk
  have hh := allBranchTruncationScale_pos k
  have hz : microCutoffBase ((θ i-θ j)/allBranchTruncationScale k)=0 := by
    by_contra hn
    have hb := fixedBranchBump_support 1 (by norm_num) hn
    rw [abs_div,abs_of_pos hh] at hb
    have ht := (div_lt_iff₀ hh).mp hb
    linarith
  simp [compactGuardedPairWeight,allBranchSelectedGuard,hz]

end
end IsingBulk.Tail
