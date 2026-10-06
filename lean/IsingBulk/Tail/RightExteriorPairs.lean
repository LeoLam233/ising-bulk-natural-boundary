import IsingBulk.Tail.CompactRootContinuation
import IsingBulk.Tail.UltraHighPairs
import IsingBulk.Algebra.SchurMobius

/-! A source-equivalent one-Pfaffian bound on right exterior charts: the
Cayley images of roots with Re W>1 lie in an acute common sector. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First

def rootCayley (z : ℂ) : ℂ := (1+z)/(1-z)

theorem rootCayley_re_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (rootCayley z).re := by
  have hz1 : 1-z ≠ 0 := by
    intro h
    have he : z = 1 := (sub_eq_zero.mp h).symm
    simp [he] at hz
  have hnorm : Complex.normSq z < 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg z]
  have he : (rootCayley z).re = (1-Complex.normSq z)/Complex.normSq (1-z) := by
    simp only [rootCayley, Complex.div_re, Complex.add_re, Complex.one_re,
      Complex.sub_re, Complex.add_im, Complex.one_im, zero_add, Complex.sub_im,
      zero_sub, Complex.normSq_apply]
    ring
  rw [he]
  exact div_pos (by linarith) (Complex.normSq_pos.mpr hz1)

theorem rootCayley_sector {W z : ℂ} (hz : ‖z‖ < 1)
    (hroot : z^2-2*W*z+1=0) (hW : 1 < W.re) :
    |(rootCayley z).im| < (rootCayley z).re := by
  have hz0 := quadratic_root_ne_zero hroot
  have hz1 : 1-z ≠ 0 := by
    intro h
    have he : z = 1 := (sub_eq_zero.mp h).symm
    simp [he] at hz
  have he : (W-1)*((rootCayley z)^2-1)=2 := by
    dsimp [rootCayley]
    field_simp
    linear_combination -2*hroot
  have hc : (rootCayley z)^2-1 ≠ 0 := by
    intro h
    simp [h] at he
  have heq : W-1 = 2/((rootCayley z)^2-1) := (eq_div_iff hc).mpr he
  have hre := congrArg Complex.re heq
  norm_num [Complex.div_re] at hre
  change W.re-1 = 2*((rootCayley z)^2-1).re / Complex.normSq ((rootCayley z)^2-1) at hre
  have hden := Complex.normSq_pos.mpr hc
  have hs : 0 < ((rootCayley z)^2-1).re := by
    have hh := (div_pos_iff.mp (show 0 < 2*((rootCayley z)^2-1).re /
      Complex.normSq ((rootCayley z)^2-1) by linarith))
    rcases hh with h | h
    · linarith [h.1]
    · linarith [h.2]
  have hp := rootCayley_re_pos hz
  simp only [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re] at hs
  rw [abs_lt]
  constructor <;> nlinarith

theorem acute_sector_ratio_bound {x y : ℂ}
    (hx : |x.im| < x.re) (hy : |y.im| < y.re) : ‖(x-y)/(x+y)‖ ≤ 1 := by
  have hxr : 0 < x.re := (abs_nonneg _).trans_lt hx
  have hyr : 0 < y.re := (abs_nonneg _).trans_lt hy
  have hd : 0 < x.re*y.re+x.im*y.im := by
    have hm : |x.im*y.im| < x.re*y.re := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hx.le (abs_nonneg _)).trans_lt
        (mul_lt_mul_of_pos_left hy hxr)
    have hn := neg_abs_le (x.im*y.im)
    linarith
  have hsq : Complex.normSq (x-y) ≤ Complex.normSq (x+y) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im]
    nlinarith
  have hn : ‖x-y‖ ≤ ‖x+y‖ := by
    rw [← Complex.sq_norm, ← Complex.sq_norm] at hsq
    nlinarith [norm_nonneg (x-y),norm_nonneg (x+y)]
  have hxy : x+y ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re] at hr
    linarith
  rw [norm_div]
  exact (div_le_one (norm_pos_iff.mpr hxy)).mpr hn

/-- Roots over the right half-plane share an acute Cayley sector, so the
whole root pair product contracts on a genuine complex chart crossing the
positive exterior real axis. -/
theorem right_half_plane_root_pair_norm {W V z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1)
    (hzq : z^2-2*W*z+1=0) (hwq : w^2-2*V*w+1=0)
    (hW : 1 < W.re) (hV : 1 < V.re) : ‖pairKernel z w‖ ≤ 1 := by
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have hw1 : w ≠ 1 := by intro h; simp [h] at hw
  have he := Schur.mobius_kernel hz1 hw1 (one_sub_mul_ne_zero_of_norm_lt_one hz hw)
  change (rootCayley z-rootCayley w)/(rootCayley z+rootCayley w) = pairKernel z w at he
  rw [← he]
  exact acute_sector_ratio_bound (rootCayley_sector hz hzq hW) (rootCayley_sector hw hwq hV)

end
end IsingBulk.Tail
