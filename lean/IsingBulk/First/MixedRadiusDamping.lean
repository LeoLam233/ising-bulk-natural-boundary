import IsingBulk.First.ComplementDamping

/-! Exact dispersion damping on mixed-radius annuli. This supplies root
admissibility and legitimate coordinatewise contour changes at fixed s. -/
namespace IsingBulk.First
noncomputable section

theorem damped_dispersion_im_mixed {x y : ℂ} (hx : ‖x‖=1) (hy : ‖y‖=1)
    (rx ry : ℝ) (s : ℂ) :
    (dispersion ((rx:ℂ)*x) ((ry:ℂ)*y) s).im = (sourceS s).im +
      (rx⁻¹-rx)/2*x.im + (ry⁻¹-ry)/2*y.im := by
  simp only [dispersion, Complex.sub_im, Complex.div_ofNat_im, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    damped_inverse_im hx, damped_inverse_im hy]
  ring

theorem inverse_radius_drop_mono {r q : ℝ} (hr : 0 < r) (hrq : r ≤ q) :
    q⁻¹-q ≤ r⁻¹-r := by
  have hq : 0 < q := hr.trans_le hrq
  have hi : q⁻¹ ≤ r⁻¹ := (inv_le_inv₀ hq hr).mpr hrq
  linarith

theorem mixed_damped_dispersion_im_positive {x y : ℂ} (hx : ‖x‖=1) (hy : ‖y‖=1)
    {r rx ry : ℝ} (hr : 0 < r) (hrx : r ≤ rx) (hry : r ≤ ry)
    (hrx1 : rx ≤ 1) (hry1 : ry ≤ 1) {s : ℂ}
    (hmargin : r⁻¹-r < (sourceS s).im) :
    0 < (dispersion ((rx:ℂ)*x) ((ry:ℂ)*y) s).im := by
  have hxpos : 0 < rx := hr.trans_le hrx
  have hypos : 0 < ry := hr.trans_le hry
  have hxinv : 1 ≤ rx⁻¹ := (one_le_inv₀ hxpos).mpr hrx1
  have hyinv : 1 ≤ ry⁻¹ := (one_le_inv₀ hypos).mpr hry1
  have hdx : 0 ≤ (rx⁻¹-rx)/2 := by linarith
  have hdy : 0 ≤ (ry⁻¹-ry)/2 := by linarith
  have hxi : -1 ≤ x.im := by
    have hh := Complex.abs_im_le_norm x
    rw [hx] at hh
    exact (abs_le.mp hh).1
  have hyi : -1 ≤ y.im := by
    have hh := Complex.abs_im_le_norm y
    rw [hy] at hh
    exact (abs_le.mp hh).1
  have hmrx := inverse_radius_drop_mono hr hrx
  have hmry := inverse_radius_drop_mono hr hry
  rw [damped_dispersion_im_mixed hx hy]
  nlinarith [mul_nonneg hdx (show 0 ≤ x.im+1 by linarith),
    mul_nonneg hdy (show 0 ≤ y.im+1 by linarith)]

theorem complex_eq_norm_mul_unit {x : ℂ} (hx : x ≠ 0) :
    ∃ u : ℂ, ‖u‖=1 ∧ x=(‖x‖:ℂ)*u := by
  refine ⟨x/(‖x‖:ℂ), ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
    exact div_self (norm_ne_zero_iff.mpr hx)
  · have hn : (‖x‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
    field_simp

theorem dispersion_im_positive_on_annulus {r : ℝ} (hr : 0 < r) {s x y : ℂ}
    (hx : r ≤ ‖x‖) (hy : r ≤ ‖y‖) (hx1 : ‖x‖ ≤ 1) (hy1 : ‖y‖ ≤ 1)
    (hmargin : r⁻¹-r < (sourceS s).im) : 0 < (dispersion x y s).im := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hr.trans_le hx)
  have hy0 : y ≠ 0 := norm_pos_iff.mp (hr.trans_le hy)
  obtain ⟨u, hu, he⟩ := complex_eq_norm_mul_unit hx0
  obtain ⟨v, hv, he'⟩ := complex_eq_norm_mul_unit hy0
  have hh := mixed_damped_dispersion_im_positive hu hv hr hx hy hx1 hy1 hmargin
  rwa [← he, ← he'] at hh

end
end IsingBulk.First
