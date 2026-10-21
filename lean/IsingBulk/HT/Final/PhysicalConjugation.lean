import IsingBulk.HT.Final.PhysicalSusceptibilityGerm

/-! Schwarz reflection of the actual HT normalization and full infinite sum.
Only conjugation is used; no evenness of the full odd-particle observable is
asserted. The beta branch is the literal principal arsinh branch. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.Final IsingBulk.First Complex

theorem temperature_sqrt_conjugate {s : ℂ} (hs : |s.im| < 1) :
    Complex.sqrt (1+(star s)^2) = star (Complex.sqrt (1+s^2)) := by
  have ha := Complex.slitPlane_arg_ne_pi
    (Or.inl (temperature_square_argument_re_pos hs) : 1+s^2 ∈ Complex.slitPlane)
  change (1+((starRingEnd ℂ) s)^2)^((2:ℂ)⁻¹) =
    (starRingEnd ℂ) ((1+s^2)^((2:ℂ)⁻¹))
  simpa only [map_add,map_one,map_pow,map_inv₀,map_ofNat] using
    Complex.conj_cpow (1+s^2) ((2:ℂ)⁻¹) ha

theorem arsinhRight_conjugate_strip {s : ℂ} (hs : |s.im| < 1) :
    arsinhRight (star s) = star (arsinhRight s) := by
  have ha := Complex.slitPlane_arg_ne_pi
    (Or.inl (temperature_log_argument_re_pos hs) : s+Complex.sqrt (1+s^2) ∈ Complex.slitPlane)
  unfold arsinhRight
  rw [temperature_sqrt_conjugate hs,← star_add]
  change Complex.log ((starRingEnd ℂ) (s+Complex.sqrt (1+s^2))) =
    (starRingEnd ℂ) (Complex.log (s+Complex.sqrt (1+s^2)))
  exact Complex.log_conj _ ha

theorem inverseTemperatureBranch_conjugate_strip (J : ℝ) {s : ℂ}
    (hs : |s.im| < 1) :
    inverseTemperatureBranch J (star s) = star (inverseTemperatureBranch J s) := by
  unfold inverseTemperatureBranch
  rw [arsinhRight_conjugate_strip hs]
  simp only [star_div₀,star_mul,star_ofNat,Complex.star_def,Complex.conj_ofReal,mul_comm]

theorem exteriorPrefactor_conjugate {t : ℂ} (ht : 1 < ‖t‖) :
    exteriorPrefactor (star t) = star (exteriorPrefactor t) := by
  simp only [exteriorPrefactor,magnetizationSquared_conjugate ht,star_mul,mul_comm]

theorem exteriorFullBulk_conjugate {t : ℂ} (ht : 1 < ‖t‖) :
    exteriorFullBulk (star t) = star (exteriorFullBulk t) := by
  simp only [exteriorFullBulk,exteriorPrefactor_conjugate ht,
    exteriorOddSeries_conjugate ht,star_mul,mul_comm]

theorem exteriorPhysicalSusceptibility_conjugate (J : ℝ) {t : ℂ}
    (ht : 1 < ‖t‖) :
    exteriorPhysicalSusceptibility J (star t) =
      star (exteriorPhysicalSusceptibility J t) := by
  have hi : ‖t⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ ht
  have hs : |(t⁻¹).im| < 1 := (Complex.abs_im_le_norm _).trans_lt hi
  simp only [exteriorPhysicalSusceptibility,← star_inv₀,
    inverseTemperatureBranch_conjugate_strip J hs,exteriorFullBulk_conjugate ht,star_mul,mul_comm]

end
end IsingBulk.HT.Final
