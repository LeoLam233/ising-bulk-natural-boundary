import IsingBulk.Analysis.JetsRegularKernel
import Mathlib.Analysis.Complex.Exponential

/-! The simple actual Z kernel on a nonwrapping fourth-quadrant microcore.
The coordinate sum is bounded below before applying a Laplace majorant. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

 theorem small_exp_gap_lower (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    ‖z‖/2 ≤ ‖1-Complex.exp z‖ := by
  have hr := Complex.norm_exp_sub_one_sub_id_le (x := z) (by linarith : ‖z‖ ≤ 1)
  have hn := norm_sub_norm_le z (Complex.exp z-1)
  have he : z-(Complex.exp z-1)=-(Complex.exp z-1-z) := by ring
  rw [he,norm_neg,norm_sub_rev (Complex.exp z) 1] at hn
  nlinarith [norm_nonneg z]

 theorem quadrant_sum_norm_lower {N : ℕ} (φ : Fin N → ℂ)
    (hr : ∀ i, 0 ≤ (φ i).re) (hi : ∀ i, (φ i).im ≤ 0) :
    (∑ i, ‖φ i‖)/2 ≤ ‖∑ i, φ i‖ := by
  have hb : (∑ i, ‖φ i‖) ≤ (∑ i, φ i).re-(∑ i, φ i).im := by
    simp only [Complex.re_sum,Complex.im_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := Complex.norm_le_abs_re_add_abs_im (φ i)
    simpa only [abs_of_nonneg (hr i),abs_of_nonpos (hi i),sub_eq_add_neg] using hh
  have hreal := Complex.re_le_norm (∑ i, φ i)
  have him := (neg_le_abs (∑ i, φ i).im).trans (Complex.abs_im_le_norm _)
  linarith

 theorem microcore_Z_gap {N : ℕ} (s : ℂ) (φ : Fin N → ℂ)
    (hr : ∀ i, 0 ≤ (φ i).re) (hi : ∀ i, (φ i).im ≤ 0)
    (hsmall : (∑ i, ‖φ i‖) ≤ 1/2) :
    (∑ i, ‖φ i‖)/4 ≤ ‖1-IsingBulk.Jets.regularZProduct s φ‖ := by
  have hn := norm_sum_le Finset.univ φ
  have hs : ‖-Complex.I*∑ i, φ i‖ ≤ 1/2 := by
    rw [norm_mul,norm_neg,Complex.norm_I,one_mul]
    exact hn.trans hsmall
  have hh := small_exp_gap_lower (-Complex.I*∑ i, φ i) hs
  rw [norm_mul,norm_neg,Complex.norm_I,one_mul] at hh
  have hq := quadrant_sum_norm_lower φ hr hi
  exact (show (∑ i, ‖φ i‖)/4 ≤ ‖∑ i, φ i‖/2 by linarith).trans hh

end
end IsingBulk.Tail
