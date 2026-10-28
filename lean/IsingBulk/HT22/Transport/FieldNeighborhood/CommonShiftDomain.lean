import IsingBulk.HT22.Transport.FieldNeighborhood.ShiftedDomain

/-! A single convex fixed-v domain across the parameter ball. -/
namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry IsingBulk.Preferred22

/-- Intersection of the moving regular domains, expressed in the unshifted
coordinate. This is the common domain used in mean-value estimates. -/
def commonShiftDomain (T : Set ℂ) (D : Set ℂ) : Set ℂ :=
  {v | ∀ t∈T, v-preferredMovingBranch t∈D}

theorem commonShiftDomain_convex (T D : Set ℂ) (hD : Convex ℝ D) :
    Convex ℝ (commonShiftDomain T D) := by
  intro x hx y hy a b ha hb hab t ht
  have hh := hD (hx t ht) (hy t ht) ha hb hab
  convert hh using 1
  simp only [smul_sub]
  have he : a • preferredMovingBranch t + b • preferredMovingBranch t =
      preferredMovingBranch t := by rw [← add_smul,hab,one_smul]
  calc
    _ = a • x + b • y - (a • preferredMovingBranch t + b • preferredMovingBranch t) := by rw [he]
    _ = _ := by abel

/-- A uniform source q-margin survives a uniformly small moving-branch
translation. The comparison involves true complex distances. -/
theorem ball_subset_commonShiftDomain (T D : Set ℂ) (t q : ℂ) (κ : ℝ)
    (hq : closedBall q κ ⊆ D)
    (hB : ∀ s∈T, ‖preferredMovingBranch t-preferredMovingBranch s‖≤κ/2) :
    closedBall (q+preferredMovingBranch t) (κ/2) ⊆ commonShiftDomain T D := by
  intro v hv s hs
  apply hq
  rw [mem_closedBall,dist_eq_norm]
  have he : v-preferredMovingBranch s-q =
      (v-(q+preferredMovingBranch t))+(preferredMovingBranch t-preferredMovingBranch s) := by ring
  rw [he]
  have hv' : ‖v-(q+preferredMovingBranch t)‖≤κ/2 := by
    simpa only [mem_closedBall,dist_eq_norm] using hv
  exact (norm_add_le _ _).trans (by linarith [hB s hs])

end
end IsingBulk.HT22
