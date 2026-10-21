import IsingBulk.HT.Final.PhysicalNormalization

/-! The original inverse-temperature branch on the whole horizontal strip
containing the unit disk. Both selected upper quadrants are covered. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.Final Complex Set

/-- The radicand stays strictly inside the right half-plane on this strip. -/
theorem temperature_square_argument_re_pos {s : ℂ} (hs : |s.im| < 1) :
    0 < (1+s^2).re := by
  have hsq : s.im^2 < 1 := by nlinarith [sq_abs s.im, abs_nonneg s.im]
  simp only [pow_two, Complex.add_re, Complex.one_re, Complex.mul_re]
  nlinarith [sq_nonneg s.re]

/-- The principal square root dominates the real part of s on the strip.
This proves that the logarithm has its actual principal analytic branch. -/
theorem temperature_log_argument_re_pos {s : ℂ} (hs : |s.im| < 1) :
    0 < (s+Complex.sqrt (1+s^2)).re := by
  have hsq : s.im^2 < 1 := by nlinarith [sq_abs s.im, abs_nonneg s.im]
  let u : ℂ := Complex.sqrt (1+s^2)
  have hroot : 0 ≤ u.re := sqrt_re_nonneg (1+s^2)
  have husq : u^2 = 1+s^2 :=
    Complex.cpow_nat_inv_pow _ (by decide : (2:ℕ) ≠ 0)
  have he := congrArg Complex.re husq
  simp only [pow_two, Complex.mul_re, Complex.add_re, Complex.one_re] at he
  have hdom : |s.re| < u.re := by
    nlinarith [sq_abs s.re, abs_nonneg s.re, sq_nonneg u.im]
  have hl := neg_abs_le s.re
  change 0 < s.re+u.re
  linarith

theorem arsinhRight_analyticAt_strip {s : ℂ} (hs : |s.im| < 1) :
    AnalyticAt ℂ arsinhRight s := by
  have hsqrt : AnalyticAt ℂ Complex.sqrt (1+s^2) :=
    Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds (Or.inl (temperature_square_argument_re_pos hs)))
  have hp : AnalyticAt ℂ (fun t : ℂ => 1+t^2) s :=
    analyticAt_const.add (analyticAt_id.pow 2)
  have hf : AnalyticAt ℂ (fun t : ℂ => t+Complex.sqrt (1+t^2)) s :=
    analyticAt_id.add (hsqrt.comp (f := fun t : ℂ => 1+t^2) hp)
  exact (analyticAt_clog (Or.inl (temperature_log_argument_re_pos hs))).comp
    (f := fun t : ℂ => t+Complex.sqrt (1+t^2)) hf

/-- This is the same literal branch as the existing physical normalization. -/
theorem arsinhRight_ne_zero_strip {s : ℂ} (hs : |s.im| < 1) (hs0 : s ≠ 0) :
    arsinhRight s ≠ 0 := by
  intro hz
  change Complex.log (s+Complex.sqrt (1+s^2)) = 0 at hz
  have harg : s+Complex.sqrt (1+s^2) ≠ 0 :=
    Complex.slitPlane_ne_zero (Or.inl (temperature_log_argument_re_pos hs))
  have he : s+Complex.sqrt (1+s^2) = 1 := by
    simpa only [hz, Complex.exp_zero] using (Complex.exp_log harg).symm
  have hr : Complex.sqrt (1+s^2) = 1-s := by linear_combination he
  have hsq : (Complex.sqrt (1+s^2))^2 = 1+s^2 :=
    Complex.cpow_nat_inv_pow _ (by decide : (2:ℕ) ≠ 0)
  rw [hr] at hsq
  have hzero : (2:ℂ)*s = 0 := by linear_combination -hsq
  exact hs0 ((mul_eq_zero.mp hzero).resolve_left (by norm_num))

theorem inverseTemperatureBranch_analyticAt_strip {J : ℝ} (hJ : 0 < J)
    {s : ℂ} (hs : |s.im| < 1) : AnalyticAt ℂ (inverseTemperatureBranch J) s := by
  have hj : (2*(J:ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hJ.ne')
  exact (arsinhRight_analyticAt_strip hs).div analyticAt_const hj

theorem inverseTemperatureBranch_regular_strip {J : ℝ} (hJ : 0 < J)
    {s : ℂ} (hs : |s.im| < 1) (hs0 : s ≠ 0) :
    AnalyticAt ℂ (inverseTemperatureBranch J) s ∧ inverseTemperatureBranch J s ≠ 0 := by
  have hj : (2*(J:ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hJ.ne')
  exact ⟨inverseTemperatureBranch_analyticAt_strip hJ hs,
    div_ne_zero (arsinhRight_ne_zero_strip hs hs0) hj⟩

theorem inverseTemperatureBranch_analyticAt_disk {J : ℝ} (hJ : 0 < J)
    {s : ℂ} (hs : ‖s‖ < 1) : AnalyticAt ℂ (inverseTemperatureBranch J) s :=
  inverseTemperatureBranch_analyticAt_strip hJ ((Complex.abs_im_le_norm s).trans_lt hs)

/-- The same physical continuation is regular on either nonimaginary part
of the unit circle, with no right-half-plane restriction. -/
theorem inverseTemperatureBranch_regular_unit_nonimaginary {J : ℝ} (hJ : 0 < J)
    {s : ℂ} (hs : ‖s‖ = 1) (hre : s.re ≠ 0) :
    AnalyticAt ℂ (inverseTemperatureBranch J) s ∧ inverseTemperatureBranch J s ≠ 0 := by
  have him : |s.im| < 1 := by
    simpa only [hs] using (Complex.abs_im_lt_norm.mpr hre)
  have hs0 : s ≠ 0 := by intro hz; apply hre; simp only [hz, Complex.zero_re]
  exact inverseTemperatureBranch_regular_strip hJ him hs0

end
end IsingBulk.HT.Final
