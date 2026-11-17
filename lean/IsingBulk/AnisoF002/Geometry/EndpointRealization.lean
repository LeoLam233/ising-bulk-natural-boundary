import IsingBulk.AnisoF002.Geometry.EndpointBridge

/-!
# Unsquared endpoint realization, including zero-real-part fibers

This file proves the realization direction of F002 Lemma 2.1 directly.
It uses only the five primitive historical spectral definitions already
permitted in the preceding checkpoint.  The proof uses an explicit unit
vector rather than dividing by either spectral coefficient or the Cramer
determinant.  Consequently it includes `x = 0` and `lam = 1`.

The displayed coordinates below are the real and imaginary parts of the
endpoint root in F002 `eq:endpointroot`, after using its endpoint equation.  They also
give a direct polynomial proof of the unsquared incidence.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic

/-- The normalized real coordinate of the endpoint root. -/
def endpointCosine (h c C q v w e : ℝ) : ℝ := C * (h * v - e * q * w) / c

/-- Its imaginary coordinate, retained to certify the closed-unit-interval bound. -/
def endpointSine (h c C q v w e : ℝ) : ℝ := C * (e * h * w + q * v) / c

theorem endpoint_unit_identity (h c H C t q v w e : ℝ)
    (hc : c ^ 2 - h ^ 2 = 1) (hC : C ^ 2 - H ^ 2 = 1)
    (ht : t ^ 2 + q ^ 2 = 1) (hv : v ^ 2 + w ^ 2 = 1)
    (he : e ^ 2 = 1) (hct : C * t = e * c * H) (hc0 : c ≠ 0) :
    endpointCosine h c C q v w e ^ 2 + endpointSine h c C q v w e ^ 2 = 1 := by
  have hct2 : C ^ 2 * t ^ 2 = c ^ 2 * H ^ 2 := by
    calc
      C ^ 2 * t ^ 2 = (C * t) ^ 2 := by ring
      _ = (e * c * H) ^ 2 := by rw [hct]
      _ = c ^ 2 * H ^ 2 := by rw [mul_pow, mul_pow, he, one_mul]
  have hnum : (C * (h * v - e * q * w)) ^ 2 +
      (C * (e * h * w + q * v)) ^ 2 = c ^ 2 := by
    linear_combination
      C ^ 2 * (h ^ 2 + q ^ 2) * hv +
      C ^ 2 * w ^ 2 * (h ^ 2 + q ^ 2) * he +
      -C ^ 2 * hc + C ^ 2 * ht + c ^ 2 * hC - hct2
  unfold endpointCosine endpointSine
  field_simp [hc0]
  nlinarith

theorem endpoint_cosine_mem_Icc (h c H C t q v w e : ℝ)
    (hc : c ^ 2 - h ^ 2 = 1) (hC : C ^ 2 - H ^ 2 = 1)
    (ht : t ^ 2 + q ^ 2 = 1) (hv : v ^ 2 + w ^ 2 = 1)
    (he : e ^ 2 = 1) (hct : C * t = e * c * H) (hc0 : c ≠ 0) :
    endpointCosine h c C q v w e ∈ Set.Icc (-1 : ℝ) 1 := by
  have hh := endpoint_unit_identity h c H C t q v w e hc hC ht hv he hct hc0
  have hs := sq_nonneg (endpointSine h c C q v w e)
  constructor <;> nlinarith [sq_nonneg (endpointCosine h c C q v w e + 1),
    sq_nonneg (endpointCosine h c C q v w e - 1)]

theorem endpoint_real_incidence (h c H C t q v w e : ℝ)
    (hc : c ^ 2 - h ^ 2 = 1) (he : e ^ 2 = 1)
    (hct : C * t = e * c * H) (hc0 : c ≠ 0) :
    c * C * t * v - h * H * q * w =
      h * t * endpointCosine h c C q v w e + e * H * v := by
  have hu : c * endpointCosine h c C q v w e = C * (h * v - e * q * w) := by
    unfold endpointCosine
    field_simp [hc0]
  apply (mul_left_cancel₀ hc0)
  linear_combination
    -h * t * hu - (h ^ 2 * v - e * h * q * w - c ^ 2 * v) * hct +
    e * c * H * v * hc + c * h * H * q * w * he

theorem endpoint_imag_incidence (h c H C t q v w e : ℝ)
    (ht : t ^ 2 + q ^ 2 = 1) (he : e ^ 2 = 1)
    (hct : C * t = e * c * H) (hc0 : c ≠ 0) :
    c * H * t * w + h * C * q * v =
      c * q * endpointCosine h c C q v w e + e * C * w := by
  have hu : c * endpointCosine h c C q v w e = C * (h * v - e * q * w) := by
    unfold endpointCosine
    field_simp [hc0]
  linear_combination
    -q * hu + e * C * w * ht - e * t * w * hct - c * H * t * w * he

/-- Every zero of the first endpoint factor has a physical unsquared endpoint
representation, including all rank-degenerate and imaginary-axis cases. -/
theorem first_endpoint_realization {lam : ℝ} {z : ℂ}
    (hedge : geometryF1 lam z.re z.im = 0) :
    ∃ u e : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 ∧ (e = 1 ∨ e = -1) ∧
      spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ) := by
  let h := Real.sinh z.re
  let c := Real.cosh z.re
  let H := Real.sinh (lam * z.re)
  let C := Real.cosh (lam * z.re)
  let t := Real.cos z.im
  let q := Real.sin z.im
  let v := Real.cos (lam * z.im)
  let w := Real.sin (lam * z.im)
  have hc : c ^ 2 - h ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq z.re
  have hC : C ^ 2 - H ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq (lam * z.re)
  have ht : t ^ 2 + q ^ 2 = 1 := Real.cos_sq_add_sin_sq z.im
  have hv : v ^ 2 + w ^ 2 = 1 := Real.cos_sq_add_sin_sq (lam * z.im)
  have hc0 : c ≠ 0 := ne_of_gt (Real.cosh_pos z.re)
  have hedge' : (C * t) ^ 2 = (c * H) ^ 2 := by
    change C ^ 2 * t ^ 2 - c ^ 2 * H ^ 2 = 0 at hedge
    nlinarith [hedge]
  have hsign : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ C * t = e * c * H := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hedge' with hs | hs
    · exact ⟨1, Or.inl rfl, by simpa using hs⟩
    · exact ⟨-1, Or.inr rfl, by simpa using hs⟩
  obtain ⟨e, he, hct⟩ := hsign
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  refine ⟨endpointCosine h c C q v w e, e,
    endpoint_cosine_mem_Icc h c H C t q v w e hc hC ht hv he2 hct hc0, he, ?_⟩
  apply Complex.ext
  · delta spectralA spectralS spectralT
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
      complex_cosh_re, complex_cosh_im, complex_sinh_re, complex_sinh_im]
    change c * t * (C * v) - h * q * (H * w) =
      h * t * endpointCosine h c C q v w e + H * v * e
    convert endpoint_real_incidence h c H C t q v w e hc he2 hct hc0 using 1 <;> ring
  · delta spectralA spectralS spectralT
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero, sub_zero,
      complex_cosh_re, complex_cosh_im, complex_sinh_re, complex_sinh_im]
    change c * t * (H * w) + h * q * (C * v) =
      c * q * endpointCosine h c C q v w e + C * w * e
    convert endpoint_imag_incidence h c H C t q v w e ht he2 hct hc0 using 1 <;> ring

/-- The axis-exchanged realization.  No reciprocal temperature sheet is used;
the reciprocal ratio only expresses the exact exchange of the two directions. -/
theorem second_endpoint_realization {lam : ℝ} {z : ℂ} (hlam : lam ≠ 0)
    (hedge : geometryF2 lam z.re z.im = 0) :
    ∃ e v : ℝ, (e = 1 ∨ e = -1) ∧ v ∈ Set.Icc (-1 : ℝ) 1 ∧
      spectralA lam z = spectralS z * (e : ℂ) + spectralT lam z * (v : ℂ) := by
  have hswap : ((lam⁻¹ : ℝ) : ℂ) * ((lam : ℂ) * z) = z := by
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam, Complex.ofReal_one, one_mul]
  have hswapR : lam⁻¹ * (lam * z.re) = z.re := by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  have hedge' : geometryF1 lam⁻¹ ((lam : ℂ) * z).re ((lam : ℂ) * z).im = 0 := by
    delta geometryF1
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero, hswapR]
    delta geometryF2 at hedge
    nlinarith [hedge]
  obtain ⟨v, e, hv, he, hinc⟩ := first_endpoint_realization hedge'
  refine ⟨e, v, he, hv, ?_⟩
  delta spectralA spectralS spectralT at hinc ⊢
  rw [hswap] at hinc
  simpa only [mul_comm, add_comm] using hinc

/-- The endpoint-locus inclusion in the actual unsquared spectral condition.
This is the first inclusion in F002 `eq:endpoint-sandwich`, with both endpoint factors and
all degenerate fibers included. -/
theorem endpoint_locus_realization {lam : ℝ} {z : ℂ} (hlam : 0 < lam)
    (hedge : geometryF1 lam z.re z.im * geometryF2 lam z.re z.im = 0) :
    ∃ u v : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 ∧ v ∈ Set.Icc (-1 : ℝ) 1 ∧
      spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ) := by
  rcases mul_eq_zero.mp hedge with hfirst | hsecond
  · obtain ⟨u, e, hu, he, hinc⟩ := first_endpoint_realization hfirst
    refine ⟨u, e, hu, ?_, hinc⟩
    rcases he with rfl | rfl <;> norm_num
  · obtain ⟨e, v, he, hv, hinc⟩ := second_endpoint_realization (ne_of_gt hlam) hsecond
    refine ⟨e, v, ?_, hv, hinc⟩
    rcases he with rfl | rfl <;> norm_num

/-- At an ordinary first-factor edge, realization now supplies the premise
that was open in the old defect-only module. -/
theorem regular_first_endpoint_exists {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : 0 < z.re)
    (hedge : geometryF1 lam z.re z.im = 0)
    (hsecond : geometryF2 lam z.re z.im ≠ 0) :
    spectralDetF002 lam z ≠ 0 ∧
    ∃ u e : ℝ, |u| < 1 ∧ (e = 1 ∨ e = -1) ∧
      spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ) := by
  obtain ⟨u, e, _, he, hinc⟩ := first_endpoint_realization hedge
  obtain ⟨hdet, hu⟩ := spectral_regular_endpoint_strict hlam hx hinc hedge hsecond
  exact ⟨hdet, u, e, hu, he, hinc⟩

end
end IsingBulk.AnisoF002.Geometry
