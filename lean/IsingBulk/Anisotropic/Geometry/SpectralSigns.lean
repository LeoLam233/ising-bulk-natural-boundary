import IsingBulk.Anisotropic.Geometry.RectangleSigns
import IsingBulk.Anisotropic.Geometry.SpectralCoordinates

namespace IsingBulk.Anisotropic
noncomputable section

theorem spectral_numerator_bounds_of_mem {lam : ℝ} {z : ℂ} (hz : z ∈ spectralSet lam) :
    spectralNU lam z ^2 ≤ spectralDet lam z ^2 ∧
    spectralNV lam z ^2 ≤ spectralDet lam z ^2 := by
  rcases hz with ⟨u,hu,v,hv,h⟩
  have he := real_coordinates_unique _ _ _ u v h
  change spectralNU lam z = spectralDet lam z*u ∧ spectralNV lam z = spectralDet lam z*v at he
  rw [he.1,he.2]
  have hu2 := (sq_le_one_iff_abs_le_one u).mpr (abs_le.mpr hu)
  have hv2 := (sq_le_one_iff_abs_le_one v).mpr (abs_le.mpr hv)
  constructor
  · nlinarith [mul_nonneg (sq_nonneg (spectralDet lam z)) (sub_nonneg.mpr hu2)]
  · nlinarith [mul_nonneg (sq_nonneg (spectralDet lam z)) (sub_nonneg.mpr hv2)]

theorem spectral_numerator_bounds_iff_signs {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hx : 0<z.re) (hq : Real.sin z.im ≠ 0 ∨ Real.sin (lam*z.im) ≠ 0) :
    (spectralNU lam z ^2 ≤ spectralDet lam z ^2 ∧ spectralNV lam z ^2 ≤ spectralDet lam z ^2) ↔
    geometryF1 lam z.re z.im * geometryF2 lam z.re z.im ≤ 0 := by
  rw [spectralNU_formula, spectralNV_formula, spectralDet_formula]
  exact rectangle_sign_criterion _ _ _ _ _ _ _ _
    (Real.sinh_pos_iff.mpr hx) (Real.sinh_pos_iff.mpr (mul_pos hlam hx))
    (Real.cosh_pos _) (Real.cosh_pos _) (Real.cosh_sq_sub_sinh_sq _)
    (Real.cosh_sq_sub_sinh_sq _) (Real.sin_sq_add_cos_sq _) (Real.sin_sq_add_cos_sq _) hq

theorem angles_nonzero_of_det_ne_zero {lam : ℝ} {z : ℂ} (hd : spectralDet lam z ≠ 0) :
    Real.sin z.im ≠ 0 ∨ Real.sin (lam*z.im) ≠ 0 := by
  by_contra h
  push Not at h
  rw [spectralDet_formula, h.1,h.2] at hd
  simp at hd

/-- Exact unsquared spectral geometry on every noncollinear right-half-plane point. -/
theorem mem_spectralSet_iff_signs_of_det_ne_zero {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hx : 0<z.re) (hd : spectralDet lam z ≠ 0) :
    z ∈ spectralSet lam ↔ geometryF1 lam z.re z.im * geometryF2 lam z.re z.im ≤ 0 := by
  rw [mem_spectralSet_iff_coordinates hd]
  have scalar (n : ℝ) : |n/spectralDet lam z| ≤ 1 ↔ n^2 ≤ spectralDet lam z^2 := by
    rw [← sq_le_one_iff_abs_le_one, div_pow, div_le_one₀ (sq_pos_of_ne_zero hd)]
  rw [spectralU, spectralV, scalar, scalar]
  exact spectral_numerator_bounds_iff_signs hlam hx (angles_nonzero_of_det_ne_zero hd)

end
end IsingBulk.Anisotropic
