import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# The correct complex Schur contraction

F002 contracts `(v-w)/(1-v*w)`, not the canceled anisotropic complete pair.
The explicit bound below is uniform over both variables in a closed unit
disk whose imaginary parts lie below `-delta`.  It is derived directly from
the complex norm identity.  No claim about the modulus of the complete
physical pair factor occurs in this development.
-/

namespace IsingBulk.AnisoF002.RegularTail
noncomputable section

def schur (v w : ℂ) : ℂ := (v - w) / (1 - v * w)

theorem schur_norm_defect (v w : ℂ) :
    ‖1 - v * w‖ ^ 2 - ‖v - w‖ ^ 2 =
      (1 - ‖v‖ ^ 2) * (1 - ‖w‖ ^ 2) + 4 * v.im * w.im := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im]
  ring

theorem schur_denominator_ne_zero {v w : ℂ}
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (him : 0 < v.im * w.im) :
    1 - v * w ≠ 0 := by
  have hv' : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hw' : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hh := schur_norm_defect v w
  have hprod := mul_nonneg hv' hw'
  intro hzero
  rw [hzero, norm_zero] at hh
  nlinarith [sq_nonneg ‖v - w‖]

theorem schur_norm_lt_one {v w : ℂ}
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (him : 0 < v.im * w.im) :
    ‖schur v w‖ < 1 := by
  have hden := schur_denominator_ne_zero hv hw him
  have hdenpos : 0 < ‖1 - v * w‖ := norm_pos_iff.mpr hden
  have hv' : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hw' : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hh := schur_norm_defect v w
  have hprod := mul_nonneg hv' hw'
  have hlt : ‖v - w‖ < ‖1 - v * w‖ := by nlinarith [norm_nonneg (v - w)]
  rw [schur, norm_div, div_lt_one hdenpos]
  exact hlt

theorem schur_uniform_squared_bound {v w : ℂ} {delta : ℝ}
    (hdelta : 0 < delta) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (himv : v.im ≤ -delta) (himw : w.im ≤ -delta) :
    ‖schur v w‖ ^ 2 ≤ 1 - delta ^ 2 := by
  have himproduct : delta ^ 2 ≤ v.im * w.im := by
    have hv' : delta ≤ -v.im := by linarith
    have hw' : delta ≤ -w.im := by linarith
    have h := mul_le_mul hv' hw'
      hdelta.le (show 0 ≤ -v.im by linarith)
    nlinarith
  have himpos : 0 < v.im * w.im := lt_of_lt_of_le (sq_pos_of_pos hdelta) himproduct
  have hden := schur_denominator_ne_zero hv hw himpos
  have hdenpos : 0 < ‖1 - v * w‖ := norm_pos_iff.mpr hden
  have hdenupper : ‖1 - v * w‖ ≤ 2 := by
    calc
      ‖1 - v * w‖ ≤ ‖(1 : ℂ)‖ + ‖v * w‖ := norm_sub_le _ _
      _ = 1 + ‖v‖ * ‖w‖ := by rw [norm_one, norm_mul]
      _ ≤ 2 := by nlinarith [mul_le_mul hv hw (norm_nonneg w) (by norm_num : (0 : ℝ) ≤ 1)]
  have hv' : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hw' : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hprod := mul_nonneg hv' hw'
  have hidentity := schur_norm_defect v w
  have hgap : 4 * delta ^ 2 ≤ ‖1 - v * w‖ ^ 2 - ‖v - w‖ ^ 2 := by
    nlinarith
  have hsqden : ‖1 - v * w‖ ^ 2 ≤ 4 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left hsqden (sq_nonneg delta)
  have hbound : ‖v - w‖ ^ 2 ≤ (1 - delta ^ 2) * ‖1 - v * w‖ ^ 2 := by
    nlinarith
  rw [schur, norm_div, div_pow, div_le_iff₀ (sq_pos_of_pos hdenpos)]
  exact hbound

end
end IsingBulk.AnisoF002.RegularTail
