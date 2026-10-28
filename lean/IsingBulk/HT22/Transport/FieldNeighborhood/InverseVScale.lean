import IsingBulk.HT22.Transport.FieldNeighborhood.ShiftedDomain
import IsingBulk.HT22.Transport.FieldNeighborhood.BaseDifferences
import IsingBulk.Preferred22.CoordinateShell
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! The small inverse-V scale comes from the actual moving branch center,
not from treating fixed-q and fixed-v parameter jets as identical. -/
namespace IsingBulk.HT22
noncomputable section
open Set Metric Geometry IsingBulk.Preferred22 Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem sourceInverseV_shift (t q : ℂ) :
    sourceInverseV t (q+preferredMovingBranch t) = deriv (preferredMovingInverse t) q := by
  unfold sourceInverseV inverseV
  have he : regularInverse t = fun v => preferredMovingInverse t (v-preferredMovingBranch t) := by
    funext v
    exact regularInverse_moving_adapter t v
  rw [he,deriv_comp_sub_const,add_sub_cancel_right]

theorem sourceInverseV_branch_center (d : PreferredBranchData) :
    ∀ᶠ t in 𝓝 (preferredSelectedPoint d), sourceInverseV t (preferredMovingBranch t)=0 := by
  filter_upwards [preferredMovingInverse_center_germ d] with t ht
  have hh := sourceInverseV_shift t 0
  simpa only [zero_add,ht.2] using hh

/-- Convexity and the actual zero at the lower inverse branch imply a
linear q estimate, hence the physical square-root scale after the proved
actual coordinate estimate is inserted. -/
theorem sourceInverseV_bound_by_coordinate (t : ℂ) (D : Set ℂ) (C : ℝ)
    (hD : Convex ℝ D) (hz : (0:ℂ)∈D)
    (hU : ∀ q∈D, AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2)
      (t,q+preferredMovingBranch t))
    (hjet : ∀ q∈D, ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2)
      (t,q+preferredMovingBranch t)‖≤C)
    (hcenter : sourceInverseV t (preferredMovingBranch t)=0)
    (q : ℂ) (hq : q∈D) :
    ‖sourceInverseV t (q+preferredMovingBranch t)‖≤C*‖q‖ := by
  let E : Set ℂ := (fun v : ℂ => v+preferredMovingBranch t) '' D
  have hE : Convex ℝ E := by
    simpa only [add_comm] using hD.translate (preferredMovingBranch t)
  have hzE : preferredMovingBranch t∈E := ⟨0,hz,by simp⟩
  have hqE : q+preferredMovingBranch t∈E := ⟨q,hq,rfl⟩
  have hUa : ∀ v∈E, AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,v) := by
    rintro v ⟨u,hu,rfl⟩
    exact hU u hu
  have hJa : ∀ v∈E, ‖fderiv ℂ (fun z : ℂ × ℂ => sourceInverseV z.1 z.2) (t,v)‖≤C := by
    rintro v ⟨u,hu,rfl⟩
    exact hjet u hu
  have hh := inverseV_pair_lipschitz t (preferredMovingBranch t) (q+preferredMovingBranch t)
    E C hE hzE hqE hUa hJa
  simpa only [hcenter,sub_zero,add_sub_cancel_right] using hh

end
end IsingBulk.HT22
