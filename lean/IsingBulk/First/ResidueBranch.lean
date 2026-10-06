import IsingBulk.First.ResidueIntegral

/-! Exact branch correspondence: the strict interior quadratic root uniquely
fixes the square-root sign in the manuscript, without a global quadrant claim. -/
namespace IsingBulk.First
noncomputable section

def sourceW (s y : ℂ) : ℂ := sourceS s-(y+y⁻¹)/2

theorem residue_quadratic_eq {s y z : ℂ}
    (h : z^2-(2*sourceS s-y-y⁻¹)*z+1=0) : z^2-2*sourceW s y*z+1=0 := by
  unfold sourceW
  linear_combination h

theorem interior_root_square_root {W z : ℂ} (h : z^2-2*W*z+1=0) :
    (W-z)^2 = W^2-1 ∧ z = W-(W-z) := by
  constructor
  · linear_combination h
  · ring

/-- Any source square-root choice whose resulting root is interior is identical
with the root used by the actual contour theorem. -/
theorem residue_root_matches_square_root {r : ℝ} {W z q : ℂ}
    (hr : r < 1) (hz : ‖z‖ < r) (hroot : z^2-2*W*z+1=0)
    (hq : q^2=W^2-1) (hchoice : ‖W-q‖ < r) : z = W-q := by
  apply quadratic_root_unique hroot _ (hz.trans hr) (hchoice.trans hr)
  linear_combination hq

theorem residueFactor_nonzero {z : ℂ} (hz : z ≠ 0) (hn : ‖z‖ < 1) : residueFactor z ≠ 0 := by
  unfold residueFactor
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num) (pow_ne_zero _ hz)
  · simpa only [pow_two] using one_sub_mul_ne_zero_of_norm_lt_one hn hn

end
end IsingBulk.First
