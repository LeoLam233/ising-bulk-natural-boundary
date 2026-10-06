import IsingBulk.Analysis.BranchSheet
import IsingBulk.First.ResidueBranch

/-! The existing explicit dispersion root on the whole upper half-plane.
Only new FIRST application lemmas are added; the audited sheet is unchanged. -/
namespace IsingBulk.First
noncomputable section
open Complex IsingBulk.Branch

/-- The reciprocal of the exterior quadratic root is the physical interior root. -/
def interiorRoot (W : ℂ) : ℂ := (inverseCosineRoot W)⁻¹

theorem sqrt_real_nonnegative (w : ℂ) : 0 ≤ (Complex.sqrt w).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem inverseCosineRoot_upper_im {W : ℂ} (hW : 0 < W.im) :
    0 < (inverseCosineRoot W).im := by
  have hs := sqrt_real_nonnegative (1-W^2)
  simp only [inverseCosineRoot, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  linarith

/-- The norm argument uses only Im W>0, not Re W>0. -/
theorem inverseCosineRoot_upper_norm {W : ℂ} (hW : 0 < W.im) :
    1 < ‖inverseCosineRoot W‖ := by
  let z := inverseCosineRoot W
  have hz : 0 < z.im := inverseCosineRoot_upper_im hW
  have ht := congrArg Complex.im (inverseCosineRoot_trace W)
  change z.im + (z⁻¹).im = (2*W).im at ht
  simp [Complex.inv_im, Complex.mul_im, neg_div] at ht
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.mpr (inverseCosineRoot_ne_zero W)
  have ht' := (div_eq_iff (ne_of_gt hn)).mp
    (show z.im / Complex.normSq z = z.im-2*W.im by linarith)
  have hns : 1 < Complex.normSq z := by
    by_contra h
    have hle : Complex.normSq z ≤ 1 := le_of_not_gt h
    nlinarith [mul_pos hW hn]
  exact Complex.one_lt_normSq_iff.mp hns

theorem interiorRoot_nonzero (W : ℂ) : interiorRoot W ≠ 0 :=
  inv_ne_zero (inverseCosineRoot_ne_zero W)

theorem interiorRoot_trace (W : ℂ) : interiorRoot W+(interiorRoot W)⁻¹=2*W := by
  simpa only [interiorRoot, inv_inv, add_comm] using inverseCosineRoot_trace W

theorem interiorRoot_quadratic (W : ℂ) : (interiorRoot W)^2-2*W*interiorRoot W+1=0 := by
  have ht := interiorRoot_trace W
  have hz := interiorRoot_nonzero W
  field_simp at ht
  linear_combination ht

theorem interiorRoot_norm_lt_one {W : ℂ} (hW : 0 < W.im) : ‖interiorRoot W‖ < 1 := by
  rw [interiorRoot, norm_inv]
  exact inv_lt_one_of_one_lt₀ (inverseCosineRoot_upper_norm hW)

theorem interiorRoot_lower_im {W : ℂ} (hW : 0 < W.im) : (interiorRoot W).im < 0 := by
  rw [interiorRoot, Complex.inv_im]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (inverseCosineRoot_upper_im hW))
    (Complex.normSq_pos.mpr (inverseCosineRoot_ne_zero W))

theorem upper_sqrt_argument_slit {W : ℂ} (hW : 0 < W.im) : 1-W^2 ∈ Complex.slitPlane := by
  by_cases hre : W.re = 0
  · left
    simp only [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re, hre, zero_mul,
      zero_sub]
    nlinarith [sq_nonneg W.im]
  · right
    simp only [Complex.sub_im, Complex.one_im, pow_two, Complex.mul_im]
    intro he
    have hh : W.re * W.im = 0 := by linarith
    exact (mul_ne_zero hre hW.ne') hh

theorem interiorRoot_differentiableAt {W : ℂ} (hW : 0 < W.im) :
    DifferentiableAt ℂ interiorRoot W := by
  have hp : DifferentiableAt ℂ (fun w : ℂ => 1-w^2) W := by fun_prop
  have hs := (Complex.differentiableAt_sqrt (upper_sqrt_argument_slit hW)).comp W hp
  have hz : DifferentiableAt ℂ inverseCosineRoot W := differentiableAt_id.add (hs.const_mul Complex.I)
  exact hz.inv (inverseCosineRoot_ne_zero W)

theorem interiorRoot_continuousOn : ContinuousOn interiorRoot {W : ℂ | 0 < W.im} :=
  fun _W hW => (interiorRoot_differentiableAt hW).continuousAt.continuousWithinAt

end
end IsingBulk.First
