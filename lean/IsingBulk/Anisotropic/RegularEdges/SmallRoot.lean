import IsingBulk.Tail.CompactRootContinuation
import IsingBulk.First.ResidueAlgebra
import IsingBulk.Anisotropic.Final.AnalyticInverse

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

/-- The physical slit complement, unlike a one-sided continuation cover. -/
def SmallRootDomain : Set ℂ := {W | W.im≠0 ∨ 1<W.re ∨ W.re< -1}

theorem smallRootDomain_isOpen : IsOpen SmallRootDomain :=
  (isOpen_ne_fun Complex.continuous_im continuous_const).union
    ((isOpen_lt continuous_const Complex.continuous_re).union (isOpen_lt Complex.continuous_re continuous_const))

theorem exists_small_root {W : ℂ} (hW : W∈SmallRootDomain) :
    ∃ z : ℂ, z^2-2*W*z+1=0 ∧ ‖z‖<1 := by
  rcases hW with hi | hr | hl
  · rcases lt_or_gt_of_ne hi with hi | hi
    · refine ⟨star (interiorRoot (star W)),?_,?_⟩
      · have h := congrArg (starRingEnd ℂ) (interiorRoot_quadratic (star W))
        simpa only [map_add,map_sub,map_mul,map_pow,map_one,map_ofNat,map_zero,starRingEnd_apply,star_star] using h
      · simpa only [norm_star] using interiorRoot_norm_lt_one
          (show 0<(star W).im by simpa only [Complex.star_def,Complex.conj_im] using neg_pos.mpr hi)
    · exact ⟨interiorRoot W,interiorRoot_quadratic W,interiorRoot_norm_lt_one hi⟩
  · exact ⟨compactLeftRoot W,compactLeftRoot_quadratic W,compactLeftRoot_norm_lt_one hr⟩
  · refine ⟨-compactLeftRoot (-W),?_,?_⟩
    · have h := compactLeftRoot_quadratic (-W)
      linear_combination h
    · simpa only [norm_neg] using compactLeftRoot_norm_lt_one
        (show 1<(-W).re by simp only [Complex.neg_re]; linarith)

@[irreducible] def smallRoot (W : ℂ) : ℂ :=
  if h : W∈SmallRootDomain then Classical.choose (exists_small_root h) else 0

theorem smallRoot_spec {W : ℂ} (hW : W∈SmallRootDomain) :
    smallRoot W^2-2*W*smallRoot W+1=0 ∧ ‖smallRoot W‖<1 := by
  simp only [smallRoot,dite_eq_left hW]
  exact Classical.choose_spec (exists_small_root hW)

theorem smallRoot_ne_zero {W : ℂ} (hW : W∈SmallRootDomain) : smallRoot W≠0 :=
  quadratic_root_ne_zero (smallRoot_spec hW).1

theorem smallRoot_eq_of_quadratic {W z : ℂ} (hW : W∈SmallRootDomain)
    (hz : z^2-2*W*z+1=0) (hn : ‖z‖<1) : smallRoot W=z :=
  quadratic_root_unique (smallRoot_spec hW).1 hz (smallRoot_spec hW).2 hn

end
end IsingBulk.Anisotropic.RegularEdges
