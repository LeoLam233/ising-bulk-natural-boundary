import IsingBulk.Anisotropic.Geometry.RealAngles
import IsingBulk.Anisotropic.Geometry.SignProfiles
import IsingBulk.Anisotropic.Geometry.HighTopology
import IsingBulk.Anisotropic.Geometry.Symmetry
import IsingBulk.Anisotropic.Geometry.PrefactorZeros

namespace IsingBulk.Anisotropic
noncomputable section

theorem geometryF1_abs (lam x y : ℝ) : geometryF1 lam |x| y = geometryF1 lam x y := by
  by_cases hx : 0≤x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    simp [geometryF1, mul_neg, Real.cosh_neg, Real.sinh_neg]

theorem geometryF2_abs (lam x y : ℝ) : geometryF2 lam |x| y = geometryF2 lam x y := by
  by_cases hx : 0≤x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    simp [geometryF2, mul_neg, Real.cosh_neg, Real.sinh_neg]

/-- Necessary exact signs, including every collinear, axis, and real-angle degeneration. -/
theorem geometry_signs_of_mem {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hz : z ∈ spectralSet lam) :
    geometryF1 lam z.re z.im * geometryF2 lam z.re z.im ≤ 0 := by
  rcases lt_trichotomy z.re 0 with hx | hx | hx
  · have h := geometry_signs_of_mem_right hlam (z := -z) (by simpa using neg_pos.mpr hx)
      ((neg_mem_spectralSet_iff lam z).mpr hz)
    simpa [geometryF1, geometryF2, Complex.neg_re, Complex.neg_im, mul_neg,
      Real.cosh_neg, Real.sinh_neg, Real.cos_neg] using h
  · have he : z=(z.im:ℂ)*Complex.I := by apply Complex.ext <;> simp [hx]
    have h := (imaginary_geometry_iff lam z.im).mpr (he ▸ hz)
    simpa [hx] using h
  · exact geometry_signs_of_mem_right hlam hx hz

theorem omegaL_subset_spectral_complement {lam : ℝ} (hlam : 0<lam) :
    omegaL lam ⊆ (spectralSet lam)ᶜ := by
  intro z hz hs
  have hx := omegaL_re_pos hlam hz
  have hf := (negative_signs_iff_omegaL hlam hx.le).mpr hz
  exact (not_lt_of_ge (geometry_signs_of_mem hlam hs)) (mul_pos_of_neg_of_neg hf.1 hf.2)

theorem positive_signs_of_mem_omegaH {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hz : z∈omegaH lam) :
    0<geometryF1 lam z.re z.im ∧ 0<geometryF2 lam z.re z.im := by
  have hb := central_strip_bounds hlam hz.1
  have hc := Real.cos_pos_of_mem_Ioo (abs_lt.mp hb.1)
  have hC := Real.cos_pos_of_mem_Ioo (abs_lt.mp hb.2)
  have hm := lt_min_iff.mp hz.2
  have h1 := (geometryF1_pos_iff hlam (abs_nonneg z.re) z.im).mpr
    (by simpa only [abs_of_pos hc] using hm.1)
  have h2 := (geometryF2_pos_iff hlam (abs_nonneg z.re) z.im).mpr
    (by simpa only [abs_of_pos hC] using hm.2)
  exact ⟨by simpa only [geometryF1_abs] using h1, by simpa only [geometryF2_abs] using h2⟩

theorem omegaH_subset_spectral_complement {lam : ℝ} (hlam : 0<lam) :
    omegaH lam ⊆ (spectralSet lam)ᶜ := by
  intro z hz hs
  have hf := positive_signs_of_mem_omegaH hlam hz
  exact (not_lt_of_ge (geometry_signs_of_mem hlam hs)) (mul_pos hf.1 hf.2)

theorem omegaH_product_sq_ne_one {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hz : z∈omegaH lam) :
    spectralProduct lam z^2 ≠ 1 :=
  product_sq_ne_one_of_not_mem_spectralSet (omegaH_subset_spectral_complement hlam hz)

theorem omegaL_product_sq_ne_one {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hz : z∈omegaL lam) :
    spectralProduct lam z^2 ≠ 1 :=
  product_sq_ne_one_of_not_mem_spectralSet (omegaL_subset_spectral_complement hlam hz)

end
end IsingBulk.Anisotropic
