import IsingBulk.AnisoF002.C03.PhysicalAxisCoefficients

/-! # Exact physical domains and regular frontiers under lattice-axis exchange -/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.AnisoF002.Geometry Set

theorem physical_profilePInv_axis {lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    profilePInvF002 lam⁻¹ u = lam * profileQInvF002 lam u := by
  apply (profileP_strictMono (inv_pos.mpr hlam)).injective
  rw [profileP_rightInverse (inv_pos.mpr hlam),
    ← profileQ_eq_axis_exchange hlam.ne', profileQ_rightInverse hlam]

theorem physical_profileQInv_axis {lam : ℝ} (hlam : 0 < lam) (u : ℝ) :
    profileQInvF002 lam⁻¹ u = lam * profilePInvF002 lam u := by
  apply (profileQ_strictMono (inv_pos.mpr hlam)).injective
  rw [profileQ_rightInverse (inv_pos.mpr hlam),
    profileQ_eq_axis_exchange (inv_ne_zero hlam.ne'), inv_inv,
    inv_mul_cancel_left₀ hlam.ne', profileP_rightInverse hlam]

theorem physical_highProfile_axis {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    highProfileF002 lam⁻¹ (lam * y) = lam * highProfileF002 lam y := by
  unfold highProfileF002
  rw [inv_mul_cancel_left₀ hlam.ne', physical_profilePInv_axis hlam,
    physical_profileQInv_axis hlam, mul_min_of_nonneg _ _ hlam.le, min_comm]

theorem physical_lowProfile_axis {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    lowProfileF002 lam⁻¹ (lam * y) = lam * lowProfileF002 lam y := by
  unfold lowProfileF002
  rw [inv_mul_cancel_left₀ hlam.ne', physical_profilePInv_axis hlam,
    physical_profileQInv_axis hlam, mul_max_of_nonneg _ _ hlam.le, max_comm]

theorem physical_highStripWidth_axis {lam : ℝ} (hlam : 0 < lam) :
    highStripWidthF002 lam⁻¹ = lam * highStripWidthF002 lam := by
  unfold highStripWidthF002
  rcases le_total lam 1 with h | h
  · rw [max_eq_left h, max_eq_right ((one_le_inv₀ hlam).mpr h)]
    field_simp
  · rw [max_eq_right h, max_eq_left ((inv_le_one₀ hlam).mpr h)]
    field_simp

theorem physical_high_domain_axis {lam : ℝ} (hlam : 0 < lam) (z : ℂ) :
    (lam : ℂ) * z ∈ omegaH lam⁻¹ ↔ z ∈ omegaH lam := by
  change (lam : ℂ) * z ∈ omegaHF002 lam⁻¹ ↔ z ∈ omegaHF002 lam
  simp only [omegaHF002, mem_ofPred_eq, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero,
    physical_highProfile_axis hlam, physical_highStripWidth_axis hlam,
    abs_mul, abs_of_pos hlam, mul_lt_mul_iff_right₀ hlam]

theorem physical_low_domain_axis {lam : ℝ} (hlam : 0 < lam) (z : ℂ) :
    (lam : ℂ) * z ∈ omegaL lam⁻¹ ↔ z ∈ omegaL lam := by
  change (lam : ℂ) * z ∈ omegaLF002 lam⁻¹ ↔ z ∈ omegaLF002 lam
  simp only [omegaLF002, mem_ofPred_eq, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, sub_zero,
    physical_lowProfile_axis hlam, mul_lt_mul_iff_right₀ hlam]

theorem physical_frontier_axis {lam : ℝ} (hlam : lam ≠ 0) {D E : Set ℂ}
    (hDE : ∀ w, (lam : ℂ) * w ∈ E ↔ w ∈ D) (z : ℂ) :
    (lam : ℂ) * z ∈ frontier E ↔ z ∈ frontier D := by
  let H := Homeomorph.mulLeft₀ (lam : ℂ) (Complex.ofReal_ne_zero.mpr hlam)
  have hp : H ⁻¹' E = D := by ext w; exact hDE w
  have hh := H.preimage_frontier E
  rw [hp] at hh
  exact Set.ext_iff.mp hh z

theorem physical_profileDifference_axis {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    profileDifferenceF002 lam⁻¹ (lam * y) = -lam ^ 2 * profileDifferenceF002 lam y := by
  unfold profileDifferenceF002 signedProfileRF002 signedProfileUF002
  rw [inv_mul_cancel_left₀ hlam.ne', physical_profilePInv_axis hlam, physical_profileQInv_axis hlam]
  ring

theorem physical_regularBoundary_axis {lam : ℝ} (hlam : 0 < lam) {D E : Set ℂ}
    (hDE : ∀ w, (lam : ℂ) * w ∈ E ↔ w ∈ D) {z : ℂ}
    (hz : z ∈ regularBoundaryF002 lam D) :
    (lam : ℂ) * z ∈ regularBoundaryF002 lam⁻¹ E := by
  refine ⟨(physical_frontier_axis hlam.ne' hDE z).mpr hz.1, ?_, ?_⟩
  · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_ne_zero hlam.ne' hz.2.1
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      physical_profileDifference_axis hlam]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hlam.ne')) hz.2.2

end
end IsingBulk.AnisoF002.RegularTail.C03
