import IsingBulk.Anisotropic.Geometry.SpectralAlgebra

namespace IsingBulk.Anisotropic
noncomputable section

/-- Negation changes both representing cosines, and preserves the unsquared set. -/
theorem neg_mem_spectralSet_iff (lam : ℝ) (z : ℂ) :
    -z ∈ spectralSet lam ↔ z ∈ spectralSet lam := by
  have aux : ∀ z : ℂ, z ∈ spectralSet lam → -z ∈ spectralSet lam := by
    intro w ⟨u, hu, v, hv, h⟩
    refine ⟨-u, ⟨by linarith [hu.2], by linarith [hu.1]⟩,
      -v, ⟨by linarith [hv.2], by linarith [hv.1]⟩, ?_⟩
    simpa [spectralA, spectralS, spectralT, Complex.cosh_neg, Complex.sinh_neg] using h
  exact ⟨fun h => by simpa using aux (-z) h, aux z⟩

/-- Complex conjugation preserves the real cosine parameters. -/
theorem conj_mem_spectralSet_iff (lam : ℝ) (z : ℂ) :
    star z ∈ spectralSet lam ↔ z ∈ spectralSet lam := by
  have aux : ∀ z : ℂ, z ∈ spectralSet lam → star z ∈ spectralSet lam := by
    intro w ⟨u, hu, v, hv, h⟩
    refine ⟨u, hu, v, hv, ?_⟩
    have hc := congrArg star h
    have hm : (lam : ℂ) * star w = star ((lam : ℂ) * w) := by simp
    unfold spectralA spectralS spectralT
    simp only [Complex.star_def] at hm ⊢
    rw [hm, Complex.cosh_conj, Complex.cosh_conj, Complex.sinh_conj, Complex.sinh_conj]
    simpa only [spectralA, spectralS, spectralT, star_mul, star_add,
      Complex.star_def, Complex.conj_ofReal, mul_comm] using hc
  exact ⟨fun h => by simpa using aux (star z) h, aux z⟩

/-- Formula (2.21), including every imaginary-axis degeneracy. -/
theorem imaginary_mem_spectralSet_iff (lam y : ℝ) :
    (y : ℂ) * Complex.I ∈ spectralSet lam ↔ Real.cos y * Real.cos (lam*y) = 0 := by
  have hm : (lam : ℂ) * ((y : ℂ) * Complex.I) = ((lam*y : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  constructor
  · rintro ⟨u, hu, v, hv, h⟩
    unfold spectralA spectralS spectralT at h
    rw [hm, Complex.cosh_mul_I, Complex.cosh_mul_I, Complex.sinh_mul_I,
      Complex.sinh_mul_I] at h
    have hr := congrArg Complex.re h
    simpa only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
      mul_zero, zero_mul, sub_zero, zero_sub, add_zero, neg_zero] using hr
  · intro h
    refine ⟨0, ⟨by norm_num, by norm_num⟩, 0, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp only [spectralA, hm, Complex.cosh_mul_I, Complex.ofReal_zero, mul_zero, add_zero]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_cos, ← Complex.ofReal_mul, h,
      Complex.ofReal_zero]

/-- The entire axis calculation agrees exactly with the closed real inequality. -/
theorem imaginary_geometry_iff (lam y : ℝ) :
    geometryF1 lam 0 y * geometryF2 lam 0 y ≤ 0 ↔
      (y : ℂ) * Complex.I ∈ spectralSet lam := by
  rw [imaginary_mem_spectralSet_iff]
  simp only [geometryF1, geometryF2, mul_zero, Real.cosh_zero, one_pow,
    Real.sinh_zero, zero_pow (by norm_num : 2 ≠ 0), mul_one, one_mul, sub_zero]
  rw [← mul_pow]
  constructor
  · intro h
    nlinarith [sq_nonneg (Real.cos y * Real.cos (lam*y))]
  · intro h
    rw [h]
    norm_num

end
end IsingBulk.Anisotropic
