import IsingBulk.Anisotropic.Geometry.SpectralAlgebra
import IsingBulk.Anisotropic.Geometry.Inverses

namespace IsingBulk.Anisotropic
noncomputable section

/-- Elementary exact Joukowski segment preimage, retaining both real endpoints. -/
theorem joukowski_segment_iff (s : ℂ) :
    (∃ r ∈ Set.Icc (-2 : ℝ) 2, 1 + s^2 = s * (r : ℂ)) ↔ ‖s‖ = 1 := by
  have hn : ‖s‖ = 1 ↔ Complex.normSq s = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    constructor
    · intro h; rw [h]; norm_num
    · intro h; nlinarith [norm_nonneg s]
  rw [hn]
  constructor
  · rintro ⟨r, ⟨hrlo, hrhi⟩, h⟩
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [Complex.add_re, Complex.one_re, pow_two,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
    simp only [Complex.add_im, Complex.one_im, pow_two,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at him
    rw [Complex.normSq_apply]
    change s.re*s.re + s.im*s.im = 1
    by_cases hi : s.im = 0
    · rw [hi] at hre ⊢
      rcases le_total 0 s.re with hs | hs
      · nlinarith [mul_le_mul_of_nonneg_right hrhi hs, sq_nonneg (s.re-1)]
      · nlinarith [mul_le_mul_of_nonpos_right hrlo hs, sq_nonneg (s.re+1)]
    · have hr : r = 2*s.re := by
        apply (mul_right_injective₀ hi)
        nlinarith [him]
      rw [hr] at hre
      nlinarith
  · intro h
    have hsq : s.re^2 + s.im^2 = 1 := by simpa [Complex.normSq_apply, pow_two] using h
    have hre : -1 ≤ s.re ∧ s.re ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg s.im]
    refine ⟨2*s.re, ⟨by linarith [hre.1], by linarith [hre.2]⟩, ?_⟩
    apply Complex.ext <;> simp only [Complex.add_re, Complex.one_re, pow_two,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.add_im, Complex.one_im, pow_two, Complex.mul_im, zero_add]
    · nlinarith
    · ring

/-- Exact isotropic spectral set (2.24), not a limit in the anisotropy. -/
theorem mem_spectralSet_one_iff (z : ℂ) :
    z ∈ spectralSet 1 ↔ ‖Complex.sinh z‖ = 1 := by
  have ha : spectralA 1 z = 1 + Complex.sinh z ^ 2 := by
    simp only [spectralA, Complex.ofReal_one, one_mul]
    have h := Complex.cosh_sq_sub_sinh_sq z
    linear_combination h
  rw [← joukowski_segment_iff]
  constructor
  · rintro ⟨u, hu, v, hv, h⟩
    refine ⟨u+v, ⟨by linarith [hu.1,hv.1], by linarith [hu.2,hv.2]⟩, ?_⟩
    rw [ha] at h
    simpa [spectralS, spectralT, mul_add] using h
  · rintro ⟨r, hr, h⟩
    refine ⟨r/2, ⟨by linarith [hr.1], by linarith [hr.2]⟩,
      r/2, ⟨by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
    rw [ha]
    simp only [spectralS, spectralT, Complex.ofReal_one, one_mul]
    push_cast
    linear_combination h

end
end IsingBulk.Anisotropic
