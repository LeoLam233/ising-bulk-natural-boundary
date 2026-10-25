import IsingBulk.Joint.Geometry.Basic
import IsingBulk.Anisotropic.Geometry.SpectralCoordinates
import IsingBulk.Anisotropic.Geometry.RectangleSigns

namespace IsingBulk.Joint
noncomputable section
open IsingBulk.Anisotropic

def spectralDet (K : Coupling) : ℝ := (S K).re * (T K).im - (S K).im * (T K).re
def spectralNU (K : Coupling) : ℝ := (A K).re * (T K).im - (A K).im * (T K).re
def spectralNV (K : Coupling) : ℝ := (S K).re * (A K).im - (S K).im * (A K).re
def spectralU (K : Coupling) : ℝ := spectralNU K / spectralDet K
def spectralV (K : Coupling) : ℝ := spectralNV K / spectralDet K

theorem spectral_reconstruction {K : Coupling} (hd : spectralDet K ≠ 0) :
    A K = S K * (spectralU K : ℂ) + T K * (spectralV K : ℂ) :=
  cramer_reconstruction _ _ _ hd

theorem mem_spectralSet_iff_coordinates {K : Coupling} (hd : spectralDet K ≠ 0) :
    K ∈ spectralSet ↔ |spectralU K| ≤ 1 ∧ |spectralV K| ≤ 1 := by
  constructor
  · rintro ⟨a,ha,b,hb,h⟩
    have he := real_coordinates_injective _ _ hd a b (spectralU K) (spectralV K)
      (h.symm.trans (spectral_reconstruction hd))
    rw [← he.1, ← he.2]
    exact ⟨abs_le.mpr ha, abs_le.mpr hb⟩
  · rintro ⟨ha,hb⟩
    exact ⟨spectralU K, abs_le.mp ha, spectralV K, abs_le.mp hb, spectral_reconstruction hd⟩

theorem S_re (K : Coupling) : (S K).re = Real.sinh K.1.re * Real.cos K.1.im := sinh_re_formula K.1
theorem S_im (K : Coupling) : (S K).im = Real.cosh K.1.re * Real.sin K.1.im := sinh_im_formula K.1
theorem T_re (K : Coupling) : (T K).re = Real.sinh K.2.re * Real.cos K.2.im := sinh_re_formula K.2
theorem T_im (K : Coupling) : (T K).im = Real.cosh K.2.re * Real.sin K.2.im := sinh_im_formula K.2

theorem A_re (K : Coupling) :
    (A K).re = Real.cosh K.1.re * Real.cosh K.2.re * Real.cos K.1.im * Real.cos K.2.im -
      Real.sinh K.1.re * Real.sinh K.2.re * Real.sin K.1.im * Real.sin K.2.im := by
  simp only [A, Complex.mul_re, cosh_re_formula, cosh_im_formula]
  ring

theorem A_im (K : Coupling) :
    (A K).im = Real.cosh K.1.re * Real.sinh K.2.re * Real.cos K.1.im * Real.sin K.2.im +
      Real.sinh K.1.re * Real.cosh K.2.re * Real.sin K.1.im * Real.cos K.2.im := by
  simp only [A, Complex.mul_im, cosh_re_formula, cosh_im_formula]
  ring

theorem spectralDet_formula (K : Coupling) :
    spectralDet K =
      Real.sinh K.1.re * Real.cosh K.2.re * Real.cos K.1.im * Real.sin K.2.im -
      Real.cosh K.1.re * Real.sinh K.2.re * Real.sin K.1.im * Real.cos K.2.im := by
  simp only [spectralDet, S_re, S_im, T_re, T_im]
  ring

theorem spectralNU_formula (K : Coupling) :
    spectralNU K =
      Real.cosh K.1.re * Real.cos K.1.im * Real.cos K.2.im * Real.sin K.2.im -
      Real.sinh K.1.re * Real.sinh K.2.re * Real.cosh K.2.re * Real.sin K.1.im := by
  simp only [spectralNU, A_re, A_im, T_re, T_im]
  linear_combination
    Real.sin K.2.im*Real.cos K.2.im*Real.cosh K.1.re*Real.cos K.1.im *
      Real.cosh_sq_sub_sinh_sq K.2.re -
    Real.cosh K.2.re*Real.sinh K.2.re*Real.sinh K.1.re*Real.sin K.1.im *
      Real.sin_sq_add_cos_sq K.2.im

theorem spectralNV_formula (K : Coupling) :
    spectralNV K =
      Real.sinh K.1.re * Real.cosh K.1.re * Real.sinh K.2.re * Real.sin K.2.im -
      Real.cosh K.2.re * Real.cos K.1.im * Real.sin K.1.im * Real.cos K.2.im := by
  simp only [spectralNV, A_re, A_im, S_re, S_im]
  linear_combination
    -Real.cosh K.2.re*Real.cos K.2.im*Real.sin K.1.im*Real.cos K.1.im *
      Real.cosh_sq_sub_sinh_sq K.1.re +
    Real.sinh K.2.re*Real.sin K.2.im*Real.cosh K.1.re*Real.sinh K.1.re *
      Real.sin_sq_add_cos_sq K.1.im

theorem spectralNU_sq_sub_det_sq (K : Coupling) :
    spectralNU K ^2 - spectralDet K ^2 = F2 K *
      (Real.cos K.1.im^2 * Real.sin K.2.im^2 - Real.sinh K.2.re^2 * Real.sin K.1.im^2) := by
  rw [spectralNU_formula, spectralDet_formula]
  exact numeratorU_factor _ _ _ _ _ _ _ _

theorem spectralNV_sq_sub_det_sq (K : Coupling) :
    spectralNV K ^2 - spectralDet K ^2 = -F1 K *
      (Real.sinh K.1.re^2 * Real.sin K.2.im^2 - Real.sin K.1.im^2 * Real.cos K.2.im^2) := by
  rw [spectralNV_formula, spectralDet_formula]
  convert numeratorV_factor (Real.sinh K.1.re) (Real.cosh K.1.re) (Real.sinh K.2.re)
    (Real.cosh K.2.re) (Real.cos K.1.im) (Real.sin K.1.im) (Real.cos K.2.im)
    (Real.sin K.2.im) using 1
  unfold F1
  ring

theorem spectral_numerator_bounds_of_mem {K : Coupling} (hK : K ∈ spectralSet) :
    spectralNU K ^2 ≤ spectralDet K ^2 ∧ spectralNV K ^2 ≤ spectralDet K ^2 := by
  rcases hK with ⟨a,ha,b,hb,h⟩
  have he := real_coordinates_unique _ _ _ a b h
  change spectralNU K = spectralDet K*a ∧ spectralNV K = spectralDet K*b at he
  rw [he.1,he.2]
  have ha2 := (sq_le_one_iff_abs_le_one a).mpr (abs_le.mpr ha)
  have hb2 := (sq_le_one_iff_abs_le_one b).mpr (abs_le.mpr hb)
  constructor
  · nlinarith [mul_nonneg (sq_nonneg (spectralDet K)) (sub_nonneg.mpr ha2)]
  · nlinarith [mul_nonneg (sq_nonneg (spectralDet K)) (sub_nonneg.mpr hb2)]

theorem spectral_numerator_bounds_iff_signs {K : Coupling}
    (hx : 0<K.1.re) (hu : 0<K.2.re) (hq : Real.sin K.1.im ≠ 0 ∨ Real.sin K.2.im ≠ 0) :
    (spectralNU K ^2 ≤ spectralDet K ^2 ∧ spectralNV K ^2 ≤ spectralDet K ^2) ↔
    F1 K * F2 K ≤ 0 := by
  rw [spectralNU_formula, spectralNV_formula, spectralDet_formula]
  exact rectangle_sign_criterion _ _ _ _ _ _ _ _
    (Real.sinh_pos_iff.mpr hx) (Real.sinh_pos_iff.mpr hu)
    (Real.cosh_pos _) (Real.cosh_pos _) (Real.cosh_sq_sub_sinh_sq _)
    (Real.cosh_sq_sub_sinh_sq _) (Real.sin_sq_add_cos_sq _) (Real.sin_sq_add_cos_sq _) hq

theorem angles_nonzero_of_det_ne_zero {K : Coupling} (hd : spectralDet K ≠ 0) :
    Real.sin K.1.im ≠ 0 ∨ Real.sin K.2.im ≠ 0 := by
  by_contra h
  push Not at h
  rw [spectralDet_formula, h.1,h.2] at hd
  simp at hd

theorem mem_spectralSet_iff_signs_of_det_ne_zero {K : Coupling}
    (hx : 0<K.1.re) (hu : 0<K.2.re) (hd : spectralDet K ≠ 0) :
    K ∈ spectralSet ↔ F1 K * F2 K ≤ 0 := by
  rw [mem_spectralSet_iff_coordinates hd]
  have scalar (n : ℝ) : |n/spectralDet K| ≤ 1 ↔ n^2 ≤ spectralDet K^2 := by
    rw [← sq_le_one_iff_abs_le_one, div_pow, div_le_one₀ (sq_pos_of_ne_zero hd)]
  rw [spectralU, spectralV, scalar, scalar]
  exact spectral_numerator_bounds_iff_signs hx hu (angles_nonzero_of_det_ne_zero hd)

end
end IsingBulk.Joint
