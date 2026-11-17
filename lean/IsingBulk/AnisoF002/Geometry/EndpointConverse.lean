import IsingBulk.AnisoF002.Geometry.EndpointRealization

/-!
# The converse unsquared endpoint criterion

F002 Lemma 2.1 uses the actual interval constraint on the other cosine.
The proof below retains that constraint and works without division, including
the imaginary axis and vanishing spectral coefficients.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic

theorem endpoint_norm_defect (h c H C t q v w e : ℝ)
    (hc : c ^ 2 - h ^ 2 = 1) (hC : C ^ 2 - H ^ 2 = 1)
    (ht : t ^ 2 + q ^ 2 = 1) (hv : v ^ 2 + w ^ 2 = 1)
    (he : e ^ 2 = 1) :
    (c * C * t * v - h * H * q * w - e * H * v) ^ 2 +
      (c * H * t * w + h * C * q * v - e * C * w) ^ 2 -
      ((h * t) ^ 2 + (c * q) ^ 2) =
    (c * H - e * C * t) ^ 2 - (h * w + e * q * v) ^ 2 := by
  have hs : (h * t) ^ 2 + (c * q) ^ 2 = h ^ 2 + q ^ 2 := by
    linear_combination q ^ 2 * hc + h ^ 2 * ht
  have ha : (c * t) ^ 2 + (h * q) ^ 2 = h ^ 2 + t ^ 2 := by
    linear_combination t ^ 2 * hc + h ^ 2 * ht
  have hb : (C * v) ^ 2 + (H * w) ^ 2 = H ^ 2 + v ^ 2 := by
    linear_combination v ^ 2 * hC + H ^ 2 * hv
  have hT : (H * v) ^ 2 + (C * w) ^ 2 = H ^ 2 + w ^ 2 := by
    linear_combination w ^ 2 * hC + H ^ 2 * hv
  have hcross :
      (c * C * t * v - h * H * q * w) * (H * v) +
      (c * H * t * w + h * C * q * v) * (C * w) =
      c * C * H * t + h * q * v * w := by
    linear_combination c * C * H * t * hv + h * q * v * w * hC
  calc
    _ = ((c * t) ^ 2 + (h * q) ^ 2) * ((C * v) ^ 2 + (H * w) ^ 2) +
        ((H * v) ^ 2 + (C * w) ^ 2) - ((h * t) ^ 2 + (c * q) ^ 2) -
        2 * e * ((c * C * t * v - h * H * q * w) * (H * v) +
          (c * H * t * w + h * C * q * v) * (C * w)) := by
      linear_combination ((H * v) ^ 2 + (C * w) ^ 2) * he
    _ = (h ^ 2 + t ^ 2) * (H ^ 2 + v ^ 2) + (H ^ 2 + w ^ 2) -
        (h ^ 2 + q ^ 2) - 2 * e * (c * C * H * t + h * q * v * w) := by
      rw [ha, hb, hT, hs, hcross]
    _ = _ := by
      linear_combination -H ^ 2 * hc + (h ^ 2 + 1) * hv +
        (v ^ 2 - 1) * ht - t ^ 2 * hC + (q ^ 2 * v ^ 2 - C ^ 2 * t ^ 2) * he

theorem endpoint_signed_equation_of_incidence (h c H C t q v w e u : ℝ)
    (hc : c ^ 2 - h ^ 2 = 1) (hC : C ^ 2 - H ^ 2 = 1)
    (ht : t ^ 2 + q ^ 2 = 1) (hv : v ^ 2 + w ^ 2 = 1)
    (he : e ^ 2 = 1) (hu : u ∈ Set.Icc (-1 : ℝ) 1)
    (hre : c * C * t * v - h * H * q * w = h * t * u + e * H * v)
    (him : c * H * t * w + h * C * q * v = c * q * u + e * C * w) :
    c * H = e * C * t := by
  have hprod : (c * H - e * C * t) * (h * w + e * q * v) = 0 := by
    linear_combination h * t * him - c * q * hre -
      c * h * H * w * ht + C * t * q * v * hc - C * t * q * v * he
  rcases mul_eq_zero.mp hprod with hzero | hzero
  · exact sub_eq_zero.mp hzero
  · have hnorm := endpoint_norm_defect h c H C t q v w e hc hC ht hv he
    have hre' : c * C * t * v - h * H * q * w - e * H * v = h * t * u := by linarith
    have him' : c * H * t * w + h * C * q * v - e * C * w = c * q * u := by linarith
    rw [hre', him', hzero, zero_pow (by omega), sub_zero] at hnorm
    have hu2 : u ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (by linarith [hu.1] : 0 ≤ u + 1)]
    have hn : ((h * t) ^ 2 + (c * q) ^ 2) * (u ^ 2 - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by linarith)
    have hz : (c * H - e * C * t) ^ 2 ≤ 0 := by nlinarith [hnorm, hn]
    have hz0 : (c * H - e * C * t) ^ 2 = 0 := le_antisymm hz (sq_nonneg _)
    exact sub_eq_zero.mp ((sq_eq_zero_iff).mp hz0)

/-- An actual closed-square endpoint incidence forces the corresponding
first factor to vanish. -/
theorem first_endpoint_factor_of_incidence {lam : ℝ} {z : ℂ} {u e : ℝ}
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ)) :
    geometryF1 lam z.re z.im = 0 := by
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  have hre := congrArg Complex.re hinc
  have him := congrArg Complex.im hinc
  dsimp only [spectralA, spectralS, spectralT] at hre him
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    zero_add, add_zero, complex_cosh_re, complex_cosh_im, complex_sinh_re,
    complex_sinh_im] at hre him
  have hs := endpoint_signed_equation_of_incidence
    (Real.sinh z.re) (Real.cosh z.re)
    (Real.sinh (lam * z.re)) (Real.cosh (lam * z.re))
    (Real.cos z.im) (Real.sin z.im) (Real.cos (lam * z.im)) (Real.sin (lam * z.im))
    e u (Real.cosh_sq_sub_sinh_sq z.re) (Real.cosh_sq_sub_sinh_sq (lam * z.re))
    (Real.cos_sq_add_sin_sq z.im) (Real.cos_sq_add_sin_sq (lam * z.im)) he2 hu
    (by convert hre using 1 <;> ring) (by convert him using 1 <;> ring)
  have hsq := congrArg (fun a : ℝ => a ^ 2) hs
  delta geometryF1
  simp only [mul_pow, he2, one_mul] at hsq
  nlinarith [hsq]

/-- Exact first-factor equivalence with the unsquared endpoint incidence. -/
theorem first_endpoint_iff {lam : ℝ} {z : ℂ} :
    geometryF1 lam z.re z.im = 0 ↔
      ∃ u e : ℝ, u ∈ Set.Icc (-1 : ℝ) 1 ∧ (e = 1 ∨ e = -1) ∧
        spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ) := by
  constructor
  · exact first_endpoint_realization
  · rintro ⟨u, e, hu, he, hinc⟩
    exact first_endpoint_factor_of_incidence hu he hinc

/-- Axis exchange supplies the converse for the other endpoint factor. -/
theorem second_endpoint_factor_of_incidence {lam : ℝ} {z : ℂ} {e v : ℝ}
    (hlam : lam ≠ 0) (he : e = 1 ∨ e = -1) (hv : v ∈ Set.Icc (-1 : ℝ) 1)
    (hinc : spectralA lam z = spectralS z * (e : ℂ) + spectralT lam z * (v : ℂ)) :
    geometryF2 lam z.re z.im = 0 := by
  have hswap : ((lam⁻¹ : ℝ) : ℂ) * ((lam : ℂ) * z) = z := by
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam, Complex.ofReal_one, one_mul]
  have hinc' : spectralA lam⁻¹ ((lam : ℂ) * z) =
      spectralS ((lam : ℂ) * z) * (v : ℂ) +
      spectralT lam⁻¹ ((lam : ℂ) * z) * (e : ℂ) := by
    delta spectralA spectralS spectralT at hinc ⊢
    rw [hswap]
    simpa only [mul_comm, add_comm] using hinc
  have hedge := first_endpoint_factor_of_incidence hv he hinc'
  have hswapR : lam⁻¹ * (lam * z.re) = z.re := by
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  dsimp only [geometryF1] at hedge
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, hswapR] at hedge
  delta geometryF2
  nlinarith [hedge]

theorem second_endpoint_iff {lam : ℝ} {z : ℂ} (hlam : lam ≠ 0) :
    geometryF2 lam z.re z.im = 0 ↔
      ∃ e v : ℝ, (e = 1 ∨ e = -1) ∧ v ∈ Set.Icc (-1 : ℝ) 1 ∧
        spectralA lam z = spectralS z * (e : ℂ) + spectralT lam z * (v : ℂ) := by
  constructor
  · exact second_endpoint_realization hlam
  · rintro ⟨e, v, he, hv, hinc⟩
    exact second_endpoint_factor_of_incidence hlam he hv hinc

theorem endpoint_factor_of_square_boundary {lam : ℝ} {z : ℂ} {u v : ℝ}
    (hlam : 0 < lam) (hu : u ∈ Set.Icc (-1 : ℝ) 1) (hv : v ∈ Set.Icc (-1 : ℝ) 1)
    (hend : (u = 1 ∨ u = -1) ∨ (v = 1 ∨ v = -1))
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ)) :
    geometryF1 lam z.re z.im * geometryF2 lam z.re z.im = 0 := by
  rcases hend with huend | hvend
  · rw [second_endpoint_factor_of_incidence (ne_of_gt hlam) huend hv hinc, mul_zero]
  · rw [first_endpoint_factor_of_incidence hu hvend hinc, zero_mul]

end
end IsingBulk.AnisoF002.Geometry
