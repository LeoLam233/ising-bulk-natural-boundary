import IsingBulk.AnisoF002.C03.IsotropicBranchOccupancies
import IsingBulk.AnisoF002.C03.IsotropicActualCoordinates

/-!
# Actual one-variable curves with the complete occupancies held fixed

These curves connect two coordinates of one actual balanced tuple.
Holding its two full population values fixed for this one-dimensional
integration does not alter any population derivative in the previously
constructed transport current.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem fixedOccupancyShift_abs_le (η τ ρ υ θ : ℝ) (hτ : 0 ≤ τ)
    (hρ : ρ ∈ Icc 0 1) (hυ : υ ∈ Icc 0 1) :
    |τ * (ρ * lowerPeriodicBump η θ - υ * upperPeriodicBump η θ)| ≤ τ := by
  have hp := upperPeriodicBump_bounds η θ
  have hm := lowerPeriodicBump_bounds η θ
  have hpm : 0 ≤ ρ * lowerPeriodicBump η θ := mul_nonneg hρ.1 hm.1
  have hmp : 0 ≤ υ * upperPeriodicBump η θ := mul_nonneg hυ.1 hp.1
  have hpm1 : ρ * lowerPeriodicBump η θ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hρ.2 hm.2 hm.1 (by norm_num : (0 : ℝ) ≤ 1)
  have hmp1 : υ * upperPeriodicBump η θ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hυ.2 hp.2 hp.1 (by norm_num : (0 : ℝ) ≤ 1)
  rw [abs_mul, abs_of_nonneg hτ]
  have hd : |ρ * lowerPeriodicBump η θ - υ * upperPeriodicBump η θ| ≤ 1 := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hd hτ

theorem fixedOccupancyAngle_displacement (η τ ρ υ θ : ℝ) (hτ : 0 ≤ τ)
    (hρ : ρ ∈ Icc 0 1) (hυ : υ ∈ Icc 0 1) :
    ‖fixedOccupancyAngle η τ ρ υ θ - (θ : ℂ)‖ ≤ τ := by
  simpa only [fixedOccupancyAngle, sub_sub_cancel_left, norm_neg, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul] using
      fixedOccupancyShift_abs_le η τ ρ υ θ hτ hρ hυ

theorem fixedOccupancyAngle_sheet (s : ℂ) (hs : 0 < s.im)
    (η τ ρ υ θ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) (hυ : 0 ≤ υ) :
    0 < (isotropicDispersion (s, fixedOccupancyAngle η τ ρ υ θ)).im := by
  have hp := (actual_bump_sine_signs hη θ).1
  have hm := (actual_bump_sine_signs hη θ).2
  have hsign : (τ * (ρ * lowerPeriodicBump η θ - υ * upperPeriodicBump η θ)) *
      Real.sin θ ≤ 0 := by
    have h₁ := mul_nonpos_of_nonneg_of_nonpos hρ hm
    have h₂ := mul_nonneg hυ hp
    have h₃ := mul_nonpos_of_nonneg_of_nonpos hτ (show
      ρ * (lowerPeriodicBump η θ * Real.sin θ) -
        υ * (upperPeriodicBump η θ * Real.sin θ) ≤ 0 by linarith only [h₁, h₂])
    nlinarith only [h₃]
  have hsin := sinh_mul_nonpos_of_mul_nonpos hsign
  rw [fixedOccupancyAngle, isotropicDispersion_contour_im]
  linarith only [hs, hsin]

def fixedOccupancySlope (η τ ρ υ θ : ℝ) : ℂ :=
  1 - Complex.I * ((τ * (ρ * deriv (lowerPeriodicBump η) θ -
    υ * deriv (upperPeriodicBump η) θ) : ℝ) : ℂ)

theorem fixedOccupancyAngle_hasDerivAt (η τ ρ υ θ : ℝ) :
    HasDerivAt (fixedOccupancyAngle η τ ρ υ) (fixedOccupancySlope η τ ρ υ θ) θ := by
  have hp := (upperPeriodicBump_contDiff η (n := 1)).differentiable_one θ |>.hasDerivAt
  have hm := (lowerPeriodicBump_contDiff η (n := 1)).differentiable_one θ |>.hasDerivAt
  have hd := ((hm.const_mul ρ).sub (hp.const_mul υ)).const_mul τ |>.ofReal_comp
  convert! (hasDerivAt_id θ).ofReal_comp.sub (hd.const_mul Complex.I) using 1

theorem fixedOccupancySlope_norm_le (η τ ρ υ θ L : ℝ) (hτ : 0 ≤ τ)
    (hρ : ρ ∈ Icc 0 1) (hυ : υ ∈ Icc 0 1) (hL : 0 ≤ L)
    (hp : |deriv (upperPeriodicBump η) θ| ≤ L)
    (hm : |deriv (lowerPeriodicBump η) θ| ≤ L) :
    ‖fixedOccupancySlope η τ ρ υ θ‖ ≤ 1 + 2 * τ * L := by
  apply (norm_sub_le _ _).trans
  simp only [norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hτ]
  have hd : |ρ * deriv (lowerPeriodicBump η) θ - υ * deriv (upperPeriodicBump η) θ| ≤ 2 * L := by
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul, abs_of_nonneg hρ.1, abs_of_nonneg hυ.1]
    have hm' : ρ * |deriv (lowerPeriodicBump η) θ| ≤ L :=
      (mul_le_mul_of_nonneg_left hm hρ.1).trans (by nlinarith only [hρ.2, hL])
    have hp' : υ * |deriv (upperPeriodicBump η) θ| ≤ L :=
      (mul_le_mul_of_nonneg_left hp hυ.1).trans (by nlinarith only [hυ.2, hL])
    linarith only [hm', hp']
  have hh := mul_le_mul_of_nonneg_left hd hτ
  linarith only [hh]

theorem complex_sin_contour_norm_le_abs (θ h : ℝ) :
    ‖Complex.sin ((θ : ℂ) - Complex.I * (h : ℂ))‖ ≤ Real.exp |h| := by
  rw [complex_sin_contour]
  apply (norm_sub_le _ _).trans
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (Real.cosh_pos h), Real.abs_sinh]
  rw [← Real.cosh_add_sinh, Real.cosh_abs]
  have hs := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one θ) (Real.cosh_pos h).le
  have hc := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (Real.sinh_nonneg_iff.mpr (abs_nonneg h))
  linarith only [hs, hc]

def fixedOccupancyRegularCurve (s : ℂ) (η τ ρ υ : ℝ) (θ : ℝ) : ℂ :=
  physicalRegularCoordinate (s, fixedOccupancyAngle η τ ρ υ θ)

def fixedOccupancyRegularSlope (s : ℂ) (η τ ρ υ : ℝ) (θ : ℝ) : ℂ :=
  (1 - Complex.sin (fixedOccupancyAngle η τ ρ υ θ) /
    Complex.sin (upperPhysicalPhase (isotropicDispersion (s, fixedOccupancyAngle η τ ρ υ θ)))) *
      fixedOccupancySlope η τ ρ υ θ

theorem fixedOccupancyRegularCurve_hasDerivAt (s : ℂ) (hs : 0 < s.im)
    (η τ ρ υ θ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) (hυ : 0 ≤ υ) :
    HasDerivAt (fixedOccupancyRegularCurve s η τ ρ υ)
      (fixedOccupancyRegularSlope s η τ ρ υ θ) θ := by
  have hd := (hasDerivAt_const θ s).prodMk (fixedOccupancyAngle_hasDerivAt η τ ρ υ θ)
  have hf := (physicalRegularCoordinate_hasFDerivAt _
    (fixedOccupancyAngle_sheet s hs η τ ρ υ θ hη hτ hρ hυ)).restrictScalars ℝ
  have hc := hf.comp_hasDerivAt θ hd
  have he : (physicalCoordinateDifferential (s, fixedOccupancyAngle η τ ρ υ θ)).restrictScalars ℝ
      (0, fixedOccupancySlope η τ ρ υ θ) = fixedOccupancyRegularSlope s η τ ρ υ θ := by
    change physicalCoordinateDifferential _ _ = _
    rw [physicalCoordinateDifferential_apply]
    simp only [fixedOccupancyRegularSlope, zero_div, sub_zero]
  rw [he] at hc
  exact hc

theorem fixedOccupancyRegularSlope_norm_bound (s : ℂ) (η τ ρ υ θ L A : ℝ)
    (hτ : τ ∈ Icc 0 1) (hρ : ρ ∈ Icc 0 1) (hυ : υ ∈ Icc 0 1) (hL : 0 ≤ L)
    (hp : |deriv (upperPeriodicBump η) θ| ≤ L)
    (hm : |deriv (lowerPeriodicBump η) θ| ≤ L)
    (hA : ‖Complex.sin (upperPhysicalPhase (isotropicDispersion
      (s, fixedOccupancyAngle η τ ρ υ θ)))‖⁻¹ ≤ A) :
    ‖fixedOccupancyRegularSlope s η τ ρ υ θ‖ ≤ (1 + Real.exp 1 * A) * (1 + 2 * L) := by
  have hs : ‖Complex.sin (fixedOccupancyAngle η τ ρ υ θ)‖ ≤ Real.exp 1 := by
    apply (complex_sin_contour_norm_le_abs θ _).trans
    apply Real.exp_le_exp.mpr
    exact (fixedOccupancyShift_abs_le η τ ρ υ θ hτ.1 hρ hυ).trans hτ.2
  have hA0 : 0 ≤ A := (inv_nonneg.mpr (norm_nonneg _)).trans hA
  have hq : ‖Complex.sin (fixedOccupancyAngle η τ ρ υ θ) /
      Complex.sin (upperPhysicalPhase (isotropicDispersion (s, fixedOccupancyAngle η τ ρ υ θ)))‖ ≤
      Real.exp 1 * A := by
    rw [norm_div, div_eq_mul_inv]
    exact mul_le_mul hs hA (inv_nonneg.mpr (norm_nonneg _)) (Real.exp_pos 1).le
  have h₁ : ‖1 - Complex.sin (fixedOccupancyAngle η τ ρ υ θ) /
      Complex.sin (upperPhysicalPhase (isotropicDispersion (s, fixedOccupancyAngle η τ ρ υ θ)))‖ ≤
      1 + Real.exp 1 * A := (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add le_rfl hq)
  have h₂ := fixedOccupancySlope_norm_le η τ ρ υ θ L hτ.1 hρ hυ hL hp hm
  have h₂' : ‖fixedOccupancySlope η τ ρ υ θ‖ ≤ 1 + 2 * L :=
    h₂.trans (by nlinarith only [hτ.2, hL])
  rw [fixedOccupancyRegularSlope, norm_mul]
  exact mul_le_mul h₁ h₂' (norm_nonneg _) (by positivity)

end IsingBulk.AnisoF002.Isotropic
