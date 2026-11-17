import IsingBulk.AnisoF002.C03.RegularIsotropicMixedAttenuation
import IsingBulk.AnisoF002.C03.IsotropicOneSidedContraction

/-!
# Quantitative complete-pair denominators near the actual isotropic branch

The roots occupy the same closed lower half disk. Near the physical
branch root one, the sum of their two distances cannot cancel. The
unsquared dispersion then converts this into a bound by the sum of
the two genuine normal displacements.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open IsingBulk.AnisoF002.RegularTail
open scoped Topology

theorem first_quadrant_norm_sum {x y : ℂ}
    (hxr : 0 ≤ x.re) (hxi : 0 ≤ x.im) (hyr : 0 ≤ y.re) (hyi : 0 ≤ y.im) :
    (‖x‖ + ‖y‖) / 2 ≤ ‖x + y‖ := by
  have hcross : 0 ≤ x.re * y.re + x.im * y.im :=
    add_nonneg (mul_nonneg hxr hyr) (mul_nonneg hxi hyi)
  have hs : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 +
      2 * (x.re * y.re + x.im * y.im) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.add_re, Complex.add_im]
    ring
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x + y), sq_nonneg (‖x‖ - ‖y‖)]

theorem lower_disk_near_one_pair_gap {r s : ℂ}
    (hr : ‖r‖ ≤ 1) (hs : ‖s‖ ≤ 1) (hri : r.im ≤ 0) (hsi : s.im ≤ 0)
    (hr1 : ‖1 - r‖ ≤ 1 / 4) (hs1 : ‖1 - s‖ ≤ 1 / 4) :
    (‖1 - r‖ + ‖1 - s‖) / 4 ≤ ‖1 - r * s‖ := by
  have hrr : r.re ≤ 1 := (Complex.re_le_norm r).trans hr
  have hsr : s.re ≤ 1 := (Complex.re_le_norm s).trans hs
  have hsum := first_quadrant_norm_sum (x := 1 - r) (y := 1 - s)
    (by simpa using sub_nonneg.mpr hrr) (by simpa using hri)
    (by simpa using sub_nonneg.mpr hsr) (by simpa using hsi)
  have hrev := norm_sub_norm_le ((1 - r) + (1 - s)) ((1 - r) * (1 - s))
  have he : ((1 - r) + (1 - s)) - (1 - r) * (1 - s) = 1 - r * s := by ring
  rw [he, norm_mul] at hrev
  have hp₁ := mul_le_mul_of_nonneg_left hs1 (norm_nonneg (1 - r))
  have hp₂ := mul_le_mul_of_nonneg_left hr1 (norm_nonneg (1 - s))
  nlinarith

theorem lower_disk_near_one_pair_gap_sq {r s : ℂ}
    (hr : ‖r‖ ≤ 1) (hs : ‖s‖ ≤ 1) (hri : r.im ≤ 0) (hsi : s.im ≤ 0)
    (hr1 : ‖1 - r‖ ≤ 1 / 4) (hs1 : ‖1 - s‖ ≤ 1 / 4) :
    (‖1 - r‖ ^ 2 + ‖1 - s‖ ^ 2) / 16 ≤ ‖1 - r * s‖ ^ 2 := by
  have h := lower_disk_near_one_pair_gap hr hs hri hsi hr1 hs1
  have hh := sq_le_sq₀ (by positivity : 0 ≤ (‖1 - r‖ + ‖1 - s‖) / 4)
    (norm_nonneg (1 - r * s)) |>.mpr h
  nlinarith [mul_nonneg (norm_nonneg (1 - r)) (norm_nonneg (1 - s))]

theorem reciprocal_root_distance_one_sq {W r : ℂ}
    (hp : r ^ 2 - 2 * W * r + 1 = 0) :
    ‖1 - r‖ ^ 2 = 2 * ‖W - 1‖ * ‖r‖ := by
  have he : (1 - r) ^ 2 = 2 * (W - 1) * r := by linear_combination hp
  have hn := congrArg norm he
  simpa only [norm_pow, norm_mul, Complex.norm_two] using hn

theorem near_one_pair_gap_of_imaginary_parts {W V r s : ℂ} {c : ℝ}
    (hc : 0 ≤ c)
    (hpr : r ^ 2 - 2 * W * r + 1 = 0) (hps : s ^ 2 - 2 * V * s + 1 = 0)
    (hrc : c ≤ ‖r‖) (hsc : c ≤ ‖s‖)
    (hr : ‖r‖ ≤ 1) (hs : ‖s‖ ≤ 1) (hri : r.im ≤ 0) (hsi : s.im ≤ 0)
    (hr1 : ‖1 - r‖ ≤ 1 / 4) (hs1 : ‖1 - s‖ ≤ 1 / 4) :
    (c / 8) * (W.im + V.im) ≤ ‖1 - r * s‖ ^ 2 := by
  have hWi : W.im ≤ ‖W - 1‖ := by
    have h := Complex.im_le_norm (W - 1)
    simpa using h
  have hVi : V.im ≤ ‖V - 1‖ := by
    have h := Complex.im_le_norm (V - 1)
    simpa using h
  have hrlo := mul_le_mul hWi hrc hc (norm_nonneg (W - 1))
  have hslo := mul_le_mul hVi hsc hc (norm_nonneg (V - 1))
  have hdr := reciprocal_root_distance_one_sq hpr
  have hds := reciprocal_root_distance_one_sq hps
  have hgap := lower_disk_near_one_pair_gap_sq hr hs hri hsi hr1 hs1
  nlinarith

theorem schur_norm_le_one_same_norm_side {u v : ℂ}
    (him : 0 ≤ u.im * v.im)
    (hn : (‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1) ∨ (1 ≤ ‖u‖ ∧ 1 ≤ ‖v‖)) :
    ‖schur u v‖ ≤ 1 := by
  by_cases hd : 1 - u * v = 0
  · simp [schur, hd]
  have hp : 0 ≤ (1 - ‖u‖ ^ 2) * (1 - ‖v‖ ^ 2) := by
    rcases hn with hn | hn
    · exact mul_nonneg (by nlinarith [norm_nonneg u]) (by nlinarith [norm_nonneg v])
    · exact mul_nonneg_of_nonpos_of_nonpos (by nlinarith) (by nlinarith)
  have he := schur_norm_defect u v
  have hle : ‖u - v‖ ≤ ‖1 - u * v‖ := by
    nlinarith [norm_nonneg (u - v), norm_nonneg (1 - u * v)]
  rw [schur, norm_div]
  exact (div_le_one (norm_pos_iff.mpr hd)).mpr hle

theorem same_norm_side_reciprocal_forces_equal {u v : ℂ}
    (him : 0 ≤ u.im * v.im)
    (hn : (‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1) ∨ (1 ≤ ‖u‖ ∧ 1 ≤ ‖v‖))
    (hd : 1 - u * v = 0) : u = v := by
  have hp : 0 ≤ (1 - ‖u‖ ^ 2) * (1 - ‖v‖ ^ 2) := by
    rcases hn with hn | hn
    · exact mul_nonneg (by nlinarith [norm_nonneg u]) (by nlinarith [norm_nonneg v])
    · exact mul_nonneg_of_nonpos_of_nonpos (by nlinarith) (by nlinarith)
  have he := schur_norm_defect u v
  rw [hd, norm_zero] at he
  have hz : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end
end IsingBulk.AnisoF002.Isotropic
