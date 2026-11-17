import IsingBulk.AnisoF002.C03.IsotropicOneSidedSecants

/-!
# The actual complete-pair contraction on the entire one-sided arc

The two roots are the actual boundary spectral root and angular
exponential. The half-disk identity bounds their two Schur factors.
Off the diagonal the unsquared dispersion identifies their product
with the original canceled pair. The literal filled pair is zero
on the diagonal, including both endpoint quotients and the branch.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric
open IsingBulk.AnisoF002.RegularTail

theorem schur_norm_le_one_closed_lower (v w : ℂ)
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hvi : v.im ≤ 0) (hwi : w.im ≤ 0) :
    ‖schur v w‖ ≤ 1 := by
  by_cases hd : 1 - v * w = 0
  · simp [schur, hd]
  · have hv' : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
    have hw' : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have hprod := mul_nonneg hv' hw'
    have him := mul_nonneg_of_nonpos_of_nonpos hvi hwi
    have hh := schur_norm_defect v w
    have hle : ‖v - w‖ ≤ ‖1 - v * w‖ := by nlinarith [norm_nonneg (1 - v * w)]
    rw [schur, norm_div]
    exact (div_le_one (norm_pos_iff.mpr hd)).mpr hle

theorem schur_denominator_zero_forces_equal (v w : ℂ)
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hvi : v.im ≤ 0) (hwi : w.im ≤ 0)
    (hd : 1 - v * w = 0) : v = w := by
  have hv' : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hw' : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hprod := mul_nonneg hv' hw'
  have him := mul_nonneg_of_nonpos_of_nonpos hvi hwi
  have hh := schur_norm_defect v w
  rw [hd, norm_zero] at hh
  have hn : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem upperBoundaryRoot_im_nonpos (x : ℝ) : (upperBoundaryRoot x).im ≤ 0 := by
  simp [upperBoundaryRoot]

theorem upperBoundaryRoot_injective_on_physical {x y : ℝ} (hx : -1 < x) (hy : -1 < y)
    (h : upperBoundaryRoot x = upperBoundaryRoot y) : x = y := by
  have hp := (upperBoundaryRoot_spec x hx).1
  have hq := (upperBoundaryRoot_spec y hy).1
  rw [← h] at hq
  have he : ((x : ℂ) - (y : ℂ)) * upperBoundaryRoot x = 0 := by
    linear_combination -(hp - hq) / 2
  have hxy := (mul_eq_zero.mp he).resolve_right (upperBoundaryRoot_ne_zero x hx)
  exact Complex.ofReal_injective (sub_eq_zero.mp hxy)

theorem cosine_injective_on_oneSided {a b : ℝ}
    (ha : a ∈ Icc (-Real.pi) 0) (hb : b ∈ Icc (-Real.pi) 0)
    (h : Real.cos a = Real.cos b) : a = b := by
  have he : -a = -b := Real.strictAntiOn_cos.injOn
    ⟨by linarith [ha.2], by linarith [ha.1]⟩
    ⟨by linarith [hb.2], by linarith [hb.1]⟩ (by simpa only [Real.cos_neg] using h)
  linarith

theorem oneSided_root_denominator_ne_zero (S wa wb : ℝ) (hS : 0 < S)
    (ha : wa ∈ Icc (-Real.pi) 0) (hb : wb ∈ Icc (-Real.pi) 0) (hab : wa ≠ wb) :
    1 - upperBoundaryRoot (S - Real.cos wa) * upperBoundaryRoot (S - Real.cos wb) ≠ 0 := by
  have hxa : -1 < S - Real.cos wa := by linarith [Real.cos_le_one wa]
  have hxb : -1 < S - Real.cos wb := by linarith [Real.cos_le_one wb]
  intro hd
  have he := schur_denominator_zero_forces_equal _ _
    (upperBoundaryRoot_spec _ hxa).2.1 (upperBoundaryRoot_spec _ hxb).2.1
    (upperBoundaryRoot_im_nonpos _) (upperBoundaryRoot_im_nonpos _) hd
  have hx := upperBoundaryRoot_injective_on_physical hxa hxb he
  exact hab (cosine_injective_on_oneSided ha hb (by linarith))

theorem oneSided_angle_denominator_ne_zero (wa wb : ℝ)
    (ha : wa ∈ Icc (-Real.pi) 0) (hb : wb ∈ Icc (-Real.pi) 0) (hab : wa ≠ wb) :
    1 - Complex.exp ((wa : ℂ) * Complex.I) * Complex.exp ((wb : ℂ) * Complex.I) ≠ 0 := by
  have hi (w : ℝ) (hw : w ∈ Icc (-Real.pi) 0) :
      (Complex.exp ((w : ℂ) * Complex.I)).im ≤ 0 := by
    simpa using Real.sin_nonpos_of_nonpos_of_neg_pi_le hw.2 hw.1
  intro hd
  have he := schur_denominator_zero_forces_equal _ _
    (by rw [Complex.norm_exp_ofReal_mul_I]) (by rw [Complex.norm_exp_ofReal_mul_I])
    (hi wa ha) (hi wb hb) hd
  have hre := congrArg Complex.re he
  exact hab (cosine_injective_on_oneSided ha hb (by simpa using hre))

theorem upperBoundaryPhase_exp (x : ℝ) (hx : -1 < x) :
    Complex.exp (-(upperBoundaryPhase x * Complex.I)) = upperBoundaryRoot x := by
  have he : -(upperBoundaryPhase x * Complex.I) = Complex.log (upperBoundaryRoot x) := by
    unfold upperBoundaryPhase
    linear_combination -(Complex.log (upperBoundaryRoot x)) * Complex.I_sq
  rw [he, Complex.exp_log (upperBoundaryRoot_ne_zero x hx)]

theorem phase_pair_sine_ne_zero_of_root_gap (a b : ℂ)
    (hgap : 1 - Complex.exp (-(a * Complex.I)) * Complex.exp (-(b * Complex.I)) ≠ 0) :
    Complex.sin ((a + b) / 2) ≠ 0 := by
  have he : Complex.exp (-(((a + b) / 2) * Complex.I)) ^ 2 =
      Complex.exp (-(a * Complex.I)) * Complex.exp (-(b * Complex.I)) := by
    rw [← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  intro hz
  have hh := exp_sinh_denominator (((a + b) / 2) * Complex.I)
  rw [he, Complex.sinh_mul_I, hz, zero_mul, mul_zero] at hh
  exact hgap hh

theorem oneSided_exp_dispersion (S w : ℝ) (hS : 0 < S) :
    Complex.exp ((w : ℂ) * Complex.I) * (upperBoundaryRoot (S - Real.cos w) ^ 2 + 1) -
      2 * (S : ℂ) * Complex.exp ((w : ℂ) * Complex.I) * upperBoundaryRoot (S - Real.cos w) +
      (Complex.exp ((w : ℂ) * Complex.I) ^ 2 + 1) * upperBoundaryRoot (S - Real.cos w) = 0 := by
  have hx : -1 < S - Real.cos w := by linarith [Real.cos_le_one w]
  have hp := (upperBoundaryRoot_spec _ hx).1
  have hc : 2 * (Real.cos w : ℂ) * Complex.exp ((w : ℂ) * Complex.I) =
      Complex.exp ((w : ℂ) * Complex.I) ^ 2 + 1 := by
    rw [Complex.ofReal_cos, Complex.two_cos, add_mul]
    have he : Complex.exp (-(w : ℂ) * Complex.I) * Complex.exp ((w : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
    rw [he, ← pow_two]
  push_cast at hp
  rw [← Complex.ofReal_cos] at hp
  linear_combination Complex.exp ((w : ℂ) * Complex.I) * hp - upperBoundaryRoot (S - Real.cos w) * hc

/-- The actual filled complete pair is contractive on the whole physical
limiting one-sided arc, including the left arc and every endpoint. -/
theorem inversePairFilled_oneSided_norm_le_one (S wa wb : ℝ) (hS : 0 < S ∧ S < 2)
    (ha : wa ∈ Icc (-Real.pi) 0) (hb : wb ∈ Icc (-Real.pi) 0) :
    ‖inversePairFilled explicitRightInverse
      ((S : ℂ), oneSidedBoundaryCoordinate S wa, oneSidedBoundaryCoordinate S wb)‖ ≤ 1 := by
  by_cases hab : wa = wb
  · subst wb
    simp [inversePairFilled, inversePairAlternative, inversePairOriginal]
  · have hxa : -1 < S - Real.cos wa := by linarith [hS.1, Real.cos_le_one wa]
    have hxb : -1 < S - Real.cos wb := by linarith [hS.1, Real.cos_le_one wb]
    let r := upperBoundaryRoot (S - Real.cos wa)
    let t := upperBoundaryRoot (S - Real.cos wb)
    let y := Complex.exp ((wa : ℂ) * Complex.I)
    let z := Complex.exp ((wb : ℂ) * Complex.I)
    have hroot : 1 - r * t ≠ 0 := oneSided_root_denominator_ne_zero S wa wb hS.1 ha hb hab
    have hangle : 1 - y * z ≠ 0 := oneSided_angle_denominator_ne_zero wa wb ha hb hab
    have hp := schur_pair_eq_canceled (S := (1 : ℂ)) (T := 1) (A := (S : ℂ))
      (r := r) (s := t) (y := y) (v := z) (by norm_num)
      (Complex.exp_ne_zero _) (Complex.exp_ne_zero _) hroot hangle
      (by simpa only [one_mul] using oneSided_exp_dispersion S wa hS.1)
      (by simpa only [one_mul] using oneSided_exp_dispersion S wb hS.1)
    have hpair : inversePairFilled explicitRightInverse
        ((S : ℂ), oneSidedBoundaryCoordinate S wa, oneSidedBoundaryCoordinate S wb) =
        canceledPair 1 r t y z := by
      have hUa := (explicitRightInverse_on_oneSided_arc S wa hS ha).1
      have hUb := (explicitRightInverse_on_oneSided_arc S wb hS hb).1
      have hpa : oneSidedBoundaryCoordinate S wa - (wa : ℂ) =
          upperBoundaryPhase (S - Real.cos wa) := by dsimp [oneSidedBoundaryCoordinate]; ring
      have hpb : oneSidedBoundaryCoordinate S wb - (wb : ℂ) =
          upperBoundaryPhase (S - Real.cos wb) := by dsimp [oneSidedBoundaryCoordinate]; ring
      have hφ := phase_pair_sine_ne_zero_of_root_gap (upperBoundaryPhase (S - Real.cos wa))
        (upperBoundaryPhase (S - Real.cos wb))
        (by simpa only [upperBoundaryPhase_exp _ hxa, upperBoundaryPhase_exp _ hxb] using hroot)
      rw [inversePairFilled, hUa, hUb, hpa, hpb, ite_eq_right hφ]
      dsimp only [inversePairOriginal]
      rw [hUa, hUb, hpa, hpb]
      rw [← canceledPair_isotropic_phase (wa : ℂ) (wb : ℂ),
        upperBoundaryPhase_exp _ hxa, upperBoundaryPhase_exp _ hxb]
    have hr := schur_norm_le_one_closed_lower r t
      (upperBoundaryRoot_spec _ hxa).2.1 (upperBoundaryRoot_spec _ hxb).2.1
      (upperBoundaryRoot_im_nonpos _) (upperBoundaryRoot_im_nonpos _)
    have hy := schur_norm_le_one_closed_lower y z
      (by rw [Complex.norm_exp_ofReal_mul_I]) (by rw [Complex.norm_exp_ofReal_mul_I])
      (by simpa [y] using Real.sin_nonpos_of_nonpos_of_neg_pi_le ha.2 ha.1)
      (by simpa [z] using Real.sin_nonpos_of_nonpos_of_neg_pi_le hb.2 hb.1)
    have hp' : canceledPair 1 r t y z = schur r t * schur y z := by
      simpa only [one_div_one] using hp.symm
    rw [hpair, hp', norm_mul]
    exact (mul_le_mul hr hy (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul 1)

end IsingBulk.AnisoF002.Isotropic
