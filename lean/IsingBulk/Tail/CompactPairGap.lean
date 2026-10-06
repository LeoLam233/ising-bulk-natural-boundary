import IsingBulk.Tail.UltraHighPairs
import Mathlib.Tactic

/-! Explicit mixed compact/branch pair denominator estimates. The branch
variable may lie anywhere in the closed lower disk, including either endpoint.
No unit-disk assertion is imposed on a perturbed compact root. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First

theorem compact_pair_normSq_identity (z w : ℂ) :
    Complex.normSq z * Complex.normSq (1-z*w) =
      (Complex.normSq z*w.re-z.re)^2+(Complex.normSq z*w.im+z.im)^2 := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re,Complex.one_im,Complex.mul_re,Complex.mul_im]
  ring

theorem compact_imaginary_denominator_gap {z w : ℂ} {d : ℝ}
    (hd : 0 ≤ d) (hz : ‖z‖ ≤ 1) (hzi : z.im ≤ -d) (hwi : w.im ≤ 0) :
    d ≤ ‖1-z*w‖ := by
  have hn : 0 ≤ Complex.normSq z := Complex.normSq_nonneg z
  have hn1 : Complex.normSq z ≤ 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  have hnw : Complex.normSq z*w.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn hwi
  have hs : z.im^2 ≤ (Complex.normSq z*w.im+z.im)^2 := by
    have hp : 0 ≤ (Complex.normSq z*w.im)*z.im :=
      mul_nonneg_of_nonpos_of_nonpos hnw (by linarith)
    nlinarith [sq_nonneg (Complex.normSq z*w.im)]
  have hg : d^2 ≤ Complex.normSq z*Complex.normSq (1-z*w) := by
    rw [compact_pair_normSq_identity]
    nlinarith [sq_nonneg (Complex.normSq z*w.re-z.re)]
  have hm : Complex.normSq z*Complex.normSq (1-z*w) ≤ Complex.normSq (1-z*w) :=
    mul_le_of_le_one_left (Complex.normSq_nonneg _) hn1
  simp only [← Complex.sq_norm] at hm hg
  nlinarith [norm_nonneg (1-z*w)]

 theorem compact_norm_denominator_gap {z w : ℂ} {d : ℝ}
    (hz : ‖z‖ ≤ 1-d) (hw : ‖w‖ ≤ 1) : d ≤ ‖1-z*w‖ := by
  have hp : ‖z*w‖ ≤ 1-d := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg z) hw).trans hz
  have ht := norm_sub_norm_le (1:ℂ) (z*w)
  simp only [norm_one] at ht
  linarith

 theorem perturbed_compact_denominator_gap {z z' w : ℂ} {d : ℝ}
    (hg : d ≤ ‖1-z*w‖) (hw : ‖w‖ ≤ 1) (hm : ‖z'-z‖ ≤ d/2) :
    d/2 ≤ ‖1-z'*w‖ := by
  have hdiff : ‖(1-z*w)-(1-z'*w)‖ ≤ d/2 := by
    have he : (1-z*w)-(1-z'*w) = (z'-z)*w := by ring
    rw [he,norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hw).trans hm
  have ht' := norm_sub_norm_le (1-z*w) (1-z'*w)
  linarith

 theorem compact_pair_perturbation {z z' w : ℂ} {d : ℝ}
    (hd : 0 < d) (hg : d ≤ ‖1-z*w‖) (hw : ‖w‖ ≤ 1)
    (hm : ‖z'-z‖ ≤ d/2) :
    ‖pairKernel z' w-pairKernel z w‖ ≤ 4*‖z'-z‖/d^2 := by
  have hg' := perturbed_compact_denominator_gap hg hw hm
  have h0 : 1-z*w ≠ 0 := norm_pos_iff.mp (hd.trans_le hg)
  have h0' : 1-z'*w ≠ 0 := norm_pos_iff.mp ((half_pos hd).trans_le hg')
  have he : pairKernel z' w-pairKernel z w =
      (z'-z)*(1-w^2)/((1-z'*w)*(1-z*w)) := by
    unfold pairKernel
    field_simp [h0, h0', show 1-w*z ≠ 0 by simpa [mul_comm] using h0, show 1-w*z' ≠ 0 by simpa [mul_comm] using h0']
    ring
  have hn : ‖1-w^2‖ ≤ 2 := by
    have h := norm_sub_le (1:ℂ) (w^2)
    simp only [norm_one,norm_pow] at h
    nlinarith [norm_nonneg w]
  have hden : d*d/2 ≤ ‖1-z'*w‖*‖1-z*w‖ := by
    have h := mul_le_mul hg' hg (by linarith : 0 ≤ d) (norm_nonneg _)
    nlinarith
  rw [he,norm_div,norm_mul,norm_mul]
  calc
    _ ≤ (‖z'-z‖*2)/(d*d/2) := div_le_div₀
      (mul_nonneg (norm_nonneg _) (by norm_num))
      (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
      (by positivity) hden
    _ = 4*‖z'-z‖/d^2 := by field_simp; ring

end
end IsingBulk.Tail
