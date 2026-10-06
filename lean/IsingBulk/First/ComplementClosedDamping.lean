import IsingBulk.First.ComplementPhaseSum

/-! Closed damping inequalities for compact radial parameter sets. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

theorem damped_dispersion_im_nonnegative {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {s : ℂ}
    (hmargin : r⁻¹ - r ≤ (sourceS s).im) :
    0 ≤ (dispersion ((r : ℂ) * x) ((r : ℂ) * y) s).im := by
  have hri : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
  have hk : 0 ≤ (r⁻¹ - r) / 2 := by linarith
  have hxi : -1 ≤ x.im := by
    have := (Complex.abs_im_le_norm x)
    rw [hx] at this
    exact (abs_le.mp this).1
  have hyi : -1 ≤ y.im := by
    have := (Complex.abs_im_le_norm y)
    rw [hy] at this
    exact (abs_le.mp this).1
  rw [damped_dispersion_im hx hy]
  nlinarith [mul_nonneg hk (show 0 ≤ x.im + y.im + 2 by linarith)]

/-- Nonpositive real parts persist at the limiting unit contour as well. -/
theorem singularFactorExponent_re_nonpositive {N : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {s : ℂ}
    (hmargin : r⁻¹ - r ≤ (sourceS s).im)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (e : DoubleAngularVector N) (f : SingularFactorIndex N) (t : ℝ) :
    (singularFactorExponent r s x y e f t).re ≤ 0 := by
  have hn (z : ℂ) (hz : ‖z‖ = 1) (a : ℝ) :
      ‖angularCurve ((r : ℂ) * z) a t‖ = r := by
    rw [norm_angularCurve, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hz, mul_one]
  have hprod (z : Fin N → ℂ) (hz : ∀ i, ‖z i‖ = 1) (a : Fin N → ℝ) :
      ((∏ i, angularCurve ((r : ℂ) * z i) (a i) t) - 1).re ≤ 0 := by
    have hnorm : ‖∏ i, angularCurve ((r : ℂ) * z i) (a i) t‖ = r ^ N := by
      rw [norm_prod]
      simp only [hn _ (hz _) _, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hle := Complex.re_le_norm (∏ i, angularCurve ((r : ℂ) * z i) (a i) t)
    rw [hnorm] at hle
    have hp : r ^ N ≤ 1 := pow_le_one₀ hr.le hr1
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hpair (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (a b : ℝ) :
      (angularCurve ((r : ℂ) * z) a t * angularCurve ((r : ℂ) * w) b t - 1).re ≤ 0 := by
    have hle := Complex.re_le_norm (angularCurve ((r : ℂ) * z) a t * angularCurve ((r : ℂ) * w) b t)
    rw [norm_mul, hn z hz, hn w hw] at hle
    have hp : r*r ≤ 1 := by nlinarith
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  rcases f with b | (⟨b, i, j⟩ | i)
  · cases b
    · exact hprod x hx e.1
    · exact hprod y hy e.2
  · cases b
    · exact hpair (x i) (x j) (hx i) (hx j) (e.1 i) (e.1 j)
    · exact hpair (y i) (y j) (hy i) (hy j) (e.2 i) (e.2 j)
  · simp only [singularFactorExponent, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul, zero_sub]
    rw [angularCurve_real_mul, angularCurve_real_mul]
    exact neg_nonpos.mpr (damped_dispersion_im_nonnegative
      (by rw [norm_angularCurve, hx i]) (by rw [norm_angularCurve, hy i]) hr hr1 hmargin)


/-- The actual normalized phase remains damped on the closed parameter family. -/
theorem sourcePhaseSum_re_nonpositive_closed {N : ℕ} {ι : Type*} [Fintype ι]
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {s : ℂ} (hmargin : r⁻¹-r ≤ (sourceS s).im)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (J : ι → SingularFactorIndex N) (η : ι → ℝ) (hη : ∀ i, 0 ≤ η i)
    (u : DoubleAngularVector N) : (sourcePhaseSum r s x y J η u).re ≤ 0 := by
  change Complex.reCLM (∑ i, (η i : ℂ) * sourceAngularExponent r s x y (J i) u) ≤ 0
  rw [map_sum]
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  exact Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hη i)
    (singularFactorExponent_re_nonpositive hr hr1 hmargin x y hx hy u (J i) 1))

end
end IsingBulk.First
