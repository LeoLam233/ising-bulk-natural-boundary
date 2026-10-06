import IsingBulk.First.InteriorRoot
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact one-body norm identity and the occupancy-free square-root
majorant. Uses the physical interior root, not an assumed square-root branch. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First

theorem residueFactor_square_identity {W z : ℂ}
    (hq : z^2-2*W*z+1=0) (hd : 1-z^2 ≠ 0) :
    (residueFactor z)^2*(W^2-1)=z^2 := by
  have hpoly : (1-z^2)^2 = 4*z^2*(W^2-1) := by
    linear_combination (z^2+2*W*z+1)*hq
  unfold residueFactor
  field_simp
  linear_combination -z^2*hpoly

theorem interior_residue_norm_identity (W : ℂ) (hi : 0 < W.im) :
    ‖residueFactor (interiorRoot W)‖^2 * ‖W^2-1‖ = ‖interiorRoot W‖^2 := by
  have hn := interiorRoot_norm_lt_one hi
  have hd : 1-(interiorRoot W)^2 ≠ 0 := by
    intro he
    have hp : (interiorRoot W)^2=1 := (sub_eq_zero.mp he).symm
    have hh := congrArg norm hp
    rw [norm_pow] at hh
    norm_num at hh
    rcases hh with hh | hh <;> linarith [norm_nonneg (interiorRoot W)]
  have he := congrArg norm (residueFactor_square_identity (interiorRoot_quadratic W) hd)
  simpa only [norm_mul,norm_pow] using he

/-- The lower branch distance and the separated other branch point imply
an integrable majorant depending on |u|+ε alone. Any coupled occupancy has
already disappeared from the conclusion. -/
theorem interior_residue_sqrt_majorant (W : ℂ) (c L : ℝ)
    (hi : 0 < W.im) (hc : 0 < c) (hL : 0 < L)
    (hd : c*L ≤ ‖1-W‖) (hother : 1 ≤ ‖1+W‖) :
    ‖residueFactor (interiorRoot W)‖ ≤ 1/(Real.sqrt c*Real.sqrt L) := by
  have he := interior_residue_norm_identity W hi
  have hn := interiorRoot_norm_lt_one hi
  have hprod : c*L ≤ ‖W^2-1‖ := by
    rw [show W^2-1=-(1-W)*(1+W) by ring,norm_mul,norm_neg]
    calc
      c*L ≤ ‖1-W‖ := hd
      _ ≤ ‖1-W‖*‖1+W‖ := le_mul_of_one_le_right (norm_nonneg _) hother
  have hsq : ‖residueFactor (interiorRoot W)‖^2*(c*L) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hprod (sq_nonneg ‖residueFactor (interiorRoot W)‖)
    nlinarith [norm_nonneg (interiorRoot W)]
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  apply (le_div_iff₀ (mul_pos hsc hsL)).mpr
  have hsc2 := Real.sq_sqrt hc.le
  have hsL2 := Real.sq_sqrt hL.le
  have heq : (‖residueFactor (interiorRoot W)‖*(Real.sqrt c*Real.sqrt L))^2 =
      ‖residueFactor (interiorRoot W)‖^2*(c*L) := by
    rw [mul_pow,mul_pow,hsc2,hsL2]
  nlinarith [sq_nonneg (‖residueFactor (interiorRoot W)‖*(Real.sqrt c*Real.sqrt L)-1)]

end
end IsingBulk.Tail
