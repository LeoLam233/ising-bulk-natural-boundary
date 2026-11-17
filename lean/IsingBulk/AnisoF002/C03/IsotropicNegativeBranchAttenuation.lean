import IsingBulk.AnisoF002.C03.IsotropicNegativeBranchSector
import IsingBulk.AnisoF002.C03.IsotropicBranchCoordinateBounds

/-!
# Physical square-root attenuation on the negative branch

The actual canonical phase, rather than its quadratic approximation,
has negative imaginary part bounded below in magnitude by the branch
scale. The proof retains radial and outward attenuation together.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

theorem phase_negative_sine_im_le_sinh (φ : ℂ) (hφ : φ.im ≤ 0) :
    -(Complex.sin φ).im ≤ Real.sinh (-φ.im) := by
  have he : -(Complex.sin φ).im = Real.cos φ.re * Real.sinh (-φ.im) := by
    rw [Complex.sin_eq]
    simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sinh, Complex.add_im, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add, mul_one, Real.sinh_neg]
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right (Real.cos_le_one φ.re)
    (Real.sinh_nonneg_iff.mpr (neg_nonneg.mpr hφ))).trans_eq (one_mul _)

theorem exists_isotropic_negative_branch_phase_attenuation (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ r c : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < c ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ u h : ℝ,
        u ∈ Icc (-r) 0 → h ∈ Icc 0 r →
        c * Real.sqrt (|u| + ε + h) ≤
          -(upperPhysicalPhase (isotropicBranchDispersion α b ε u h)).im := by
  obtain ⟨rS, hrS, hrS1, hsector⟩ := exists_isotropic_negative_branch_sine_sector α b hα hb hpoint
  obtain ⟨rB, cB, _, hrB, _, hcB, _, hbounds⟩ := exists_isotropic_branch_sine_bounds α b hα hb hpoint
  obtain ⟨rA, cA, _, hrA, _, hcA, _, himag⟩ := exists_isotropic_branch_attenuation α b hα hb
  let r := min rS (min rB rA)
  let c := min (cB / (2 * Real.exp 1)) (1 / Real.sqrt 3)
  have hr : 0 < r := lt_min hrS (lt_min hrB hrA)
  have hrS' : r ≤ rS := min_le_left _ _
  have hrB' : r ≤ rB := (min_le_right _ _).trans (min_le_left _ _)
  have hrA' : r ≤ rA := (min_le_right _ _).trans (min_le_right _ _)
  have hr1 : r ≤ 1 := hrS'.trans hrS1
  have hc : 0 < c := by dsimp [c]; positivity
  have hcB' : c ≤ cB / (2 * Real.exp 1) := min_le_left _ _
  have hc3 : c ≤ 1 / Real.sqrt 3 := min_le_right _ _
  refine ⟨r, c, hr, hr1, hc, ?_⟩
  intro ε hε hεr u h hu hh
  let W := isotropicBranchDispersion α b ε u h
  let φ := upperPhysicalPhase W
  let T := |u| + ε + h
  have huabs : |u| ≤ r := by rw [abs_of_nonpos hu.2]; linarith only [hu.1]
  have hT : 0 < T := by dsimp [T]; linarith only [abs_nonneg u, hε, hh.1]
  have hT3 : T ≤ 3 := by dsimp [T]; linarith only [huabs, hεr, hh.2, hr1]
  have hW : 0 < W.im := by
    rw [isotropicBranchDispersion_im]
    exact (mul_pos hcA (by linarith only [hε, hh.1])).trans_le
      (himag ε hε (hεr.trans hrA') u h (huabs.trans hrA') ⟨hh.1, hh.2.trans hrA'⟩).1
  have hφ : φ.im < 0 := upperPhysicalPhase_im_neg W hW
  have hz := hsector ε hε (hεr.trans hrS') u h
    ⟨by linarith only [hu.1, hrS'], hu.2⟩ ⟨hh.1, hh.2.trans hrS'⟩
  have hnorm := sine_norm_le_twice_negative_im (Complex.sin φ) hz.1.le hz.2.1.le hz.2.2
  have hlo : cB * Real.sqrt T ≤ ‖Complex.sin φ‖ :=
    (hbounds ε hε (hεr.trans hrB') u h (huabs.trans hrB') ⟨hh.1, hh.2.trans hrB'⟩).1
  by_cases ha : -φ.im ≤ 1
  · have hsinh := sinh_le_exp_mul_on_interval 1 (-φ.im) ⟨(neg_pos.mpr hφ).le, ha⟩
    have him := phase_negative_sine_im_le_sinh φ hφ.le
    have hcsmall := (le_div_iff₀ (by positivity : 0 < 2 * Real.exp 1)).mp hcB'
    have hm := mul_le_mul_of_nonneg_right hcsmall (Real.sqrt_nonneg T)
    have hbound : (2 * Real.exp 1) * (c * Real.sqrt T) ≤ (2 * Real.exp 1) * (-φ.im) := by
      nlinarith only [hm, hlo, hnorm, him, hsinh]
    exact le_of_mul_le_mul_left hbound (by positivity : 0 < 2 * Real.exp 1)
  · have hsqrt := Real.sqrt_le_sqrt hT3
    have hbound : c * Real.sqrt T ≤ 1 := by
      calc
        _ ≤ (1 / Real.sqrt 3) * Real.sqrt 3 :=
          mul_le_mul hc3 hsqrt (Real.sqrt_nonneg T) (by positivity)
        _ = 1 := one_div_mul_cancel (by positivity : Real.sqrt (3 : ℝ) ≠ 0)
    exact hbound.trans (lt_of_not_ge ha).le

end IsingBulk.AnisoF002.Isotropic
