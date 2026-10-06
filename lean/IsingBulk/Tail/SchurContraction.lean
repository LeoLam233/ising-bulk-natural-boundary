import IsingBulk.Tail.UltraHighPairs
import Mathlib.Tactic

/-! Exact Schur contraction geometry on the lower closed unit half-disk.
This does not extend the unit-disk argument to protected parameter disks. -/
namespace IsingBulk.Tail
noncomputable section

theorem schur_normSq_le {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hi : 0 ≤ z.im*w.im) : Complex.normSq (z-w) ≤ Complex.normSq (1-z*w) := by
  have hz' : Complex.normSq z ≤ 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg z]
  have hw' : Complex.normSq w ≤ 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg w]
  have hp := mul_nonneg (sub_nonneg.mpr hz') (sub_nonneg.mpr hw')
  have he := schur_normSq_identity z w
  nlinarith

theorem schur_norm_le {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hi : 0 ≤ z.im*w.im) : ‖(z-w)/(1-z*w)‖ ≤ 1 := by
  rw [norm_div]
  by_cases hd : ‖1-z*w‖ = 0
  · simp [hd]
  · apply (div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd))).mpr
    have hh := schur_normSq_le hz hw hi
    rw [← Complex.sq_norm, ← Complex.sq_norm] at hh
    nlinarith [norm_nonneg (z-w), norm_nonneg (1-z*w)]

theorem schur_normSq_lt_of_interior {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1)
    (hi : 0 ≤ z.im*w.im) : Complex.normSq (z-w) < Complex.normSq (1-z*w) := by
  have hz' : Complex.normSq z < 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg z]
  have hw' : Complex.normSq w < 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg w]
  have hp := mul_pos (sub_pos.mpr hz') (sub_pos.mpr hw')
  have he := schur_normSq_identity z w
  nlinarith

theorem schur_normSq_lt_of_same_half {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hi : 0 < z.im*w.im) : Complex.normSq (z-w) < Complex.normSq (1-z*w) := by
  have hz' : Complex.normSq z ≤ 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg z]
  have hw' : Complex.normSq w ≤ 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg w]
  have hp := mul_nonneg (sub_nonneg.mpr hz') (sub_nonneg.mpr hw')
  have he := schur_normSq_identity z w
  nlinarith

theorem schur_norm_lt_of_normSq_lt {z w : ℂ}
    (h : Complex.normSq (z-w) < Complex.normSq (1-z*w)) : ‖(z-w)/(1-z*w)‖ < 1 := by
  have hn : ‖z-w‖ < ‖1-z*w‖ := by
    rw [← Complex.sq_norm, ← Complex.sq_norm] at h
    nlinarith [norm_nonneg (z-w), norm_nonneg (1-z*w)]
  rw [norm_div]
  exact (div_lt_one (lt_of_le_of_lt (norm_nonneg _) hn)).mpr hn

end
end IsingBulk.Tail
