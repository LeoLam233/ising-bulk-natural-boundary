import IsingBulk.AnisoF002.C03.IsotropicBranchPhaseBounds

/-!
# Integrable derivative majorant for the actual regular coordinate

The derivative is computed from the physical phase on the radial
branch. Its inverse-square-root majorant includes every common outward
displacement. This is the one-variable estimate used before the actual
occupancies are restored in the constrained coarea calculation.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

theorem complex_sin_contour (θ h : ℝ) :
    Complex.sin ((θ : ℂ) - Complex.I * (h : ℂ)) =
      ((Real.sin θ * Real.cosh h : ℝ) : ℂ) -
        Complex.I * ((Real.cos θ * Real.sinh h : ℝ) : ℂ) := by
  have he : (θ : ℂ) - Complex.I * (h : ℂ) =
      (θ : ℂ) + ((-h : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he, Complex.sin_add_mul_I]
  simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, Real.cosh_neg, Real.sinh_neg]
  push_cast
  ring

theorem complex_sin_contour_norm_le (θ h : ℝ) (hh : 0 ≤ h) :
    ‖Complex.sin ((θ : ℂ) - Complex.I * (h : ℂ))‖ ≤ Real.exp h := by
  rw [complex_sin_contour]
  apply (norm_sub_le _ _).trans
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (Real.cosh_pos h), abs_of_nonneg (Real.sinh_nonneg_iff.mpr hh)]
  rw [← Real.cosh_add_sinh]
  have hs := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one θ) (Real.cosh_pos h).le
  have hc := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (Real.sinh_nonneg_iff.mpr hh)
  linarith

theorem isotropicBranchDispersion_im (α b ε u h : ℝ) :
    (isotropicBranchDispersion α b ε u h).im =
      branchAttenuation b (isotropicRadialParameter α ε) u h := by
  rw [isotropicBranchDispersion, isotropicDispersion_contour_im]
  rw [show -b + u = -(b - u) by ring, Real.sin_neg]
  unfold branchAttenuation
  ring

def branchRegularCurve (α b ε h u : ℝ) : ℂ :=
  physicalRegularCoordinate (isotropicRadialParameter α ε,
    ((-b + u : ℝ) : ℂ) - Complex.I * (h : ℂ))

def branchCoordinateSlope (α b ε h u : ℝ) : ℂ :=
  1 - Complex.sin (((-b + u : ℝ) : ℂ) - Complex.I * (h : ℂ)) /
    Complex.sin (upperPhysicalPhase (isotropicBranchDispersion α b ε u h))

theorem branchRegularCurve_hasDerivAt (α b ε h u : ℝ)
    (hW : 0 < (isotropicBranchDispersion α b ε u h).im) :
    HasDerivAt (branchRegularCurve α b ε h) (branchCoordinateSlope α b ε h u) u := by
  let q : ℂ × ℂ := (isotropicRadialParameter α ε, ((-b + u : ℝ) : ℂ) - Complex.I * (h : ℂ))
  have hp : HasDerivAt
      (fun z : ℂ => (isotropicRadialParameter α ε, (-b : ℂ) + z - Complex.I * (h : ℂ)))
      (0, 1) (u : ℂ) :=
    (hasDerivAt_const (u : ℂ) _).prodMk (((hasDerivAt_id (u : ℂ)).const_add (-b : ℂ)).sub_const _)
  have hq : (isotropicRadialParameter α ε, (-b : ℂ) + (u : ℂ) - Complex.I * (h : ℂ)) = q := by
    dsimp [q]
    push_cast
    rfl
  have hf := physicalRegularCoordinate_hasFDerivAt q hW
  rw [← hq] at hf
  have hc := hf.comp_hasDerivAt (u : ℂ) hp
  have he : physicalCoordinateDifferential
      (isotropicRadialParameter α ε, (-b : ℂ) + (u : ℂ) - Complex.I * (h : ℂ)) (0, 1) =
      branchCoordinateSlope α b ε h u := by
    rw [hq, physicalCoordinateDifferential_apply]
    simp only [q, branchCoordinateSlope, isotropicBranchDispersion, mul_one, zero_div, sub_zero]
  rw [he] at hc
  have hcR : HasDerivAt
      (fun y : ℝ => physicalRegularCoordinate (isotropicRadialParameter α ε,
        (-b : ℂ) + (y : ℂ) - Complex.I * (h : ℂ))) (branchCoordinateSlope α b ε h u) u := by
    simpa only [Function.comp_def] using hc.comp_ofReal
  have hecurve : (fun y : ℝ => physicalRegularCoordinate (isotropicRadialParameter α ε,
      (-b : ℂ) + (y : ℂ) - Complex.I * (h : ℂ))) = branchRegularCurve α b ε h := by
    funext y
    simp only [branchRegularCurve, Complex.ofReal_add, Complex.ofReal_neg]
  rwa [hecurve] at hcR

/-- The true coordinate derivative has the integrable branch majorant;
outward deformation only improves its square-root denominator. -/
theorem exists_branch_coordinate_derivative_majorant (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ h ∈ Icc 0 r, ∀ u : ℝ, |u| ≤ r →
        HasDerivAt (branchRegularCurve α b ε h) (branchCoordinateSlope α b ε h u) u ∧
        ‖branchCoordinateSlope α b ε h u‖ ≤ C / Real.sqrt (|u| + ε) := by
  obtain ⟨r₁, c, _, hr₁, hr₁1, hc, _, hsin⟩ := exists_isotropic_branch_sine_bounds α b hα hb hpoint
  obtain ⟨r₂, cA, _, hr₂, _, hcA, _, hβ⟩ := exists_isotropic_branch_attenuation α b hα hb
  let r := min r₁ r₂
  let C := 2 + Real.exp 1 / c
  have hr : 0 < r := lt_min hr₁ hr₂
  have hr1 : r ≤ r₁ := min_le_left _ _
  have hr2 : r ≤ r₂ := min_le_right _ _
  have hrone : r ≤ 1 := hr1.trans hr₁1
  refine ⟨r, C, hr, hrone, by dsimp [C]; positivity, ?_⟩
  intro ε hε hεr h hh u hu
  have hatt := (hβ ε hε (hεr.trans hr2) u h (hu.trans hr2) ⟨hh.1, hh.2.trans hr2⟩).1
  have hW : 0 < (isotropicBranchDispersion α b ε u h).im := by
    rw [isotropicBranchDispersion_im]
    exact (mul_pos hcA (by linarith [hh.1])).trans_le hatt
  refine ⟨branchRegularCurve_hasDerivAt α b ε h u hW, ?_⟩
  have hlo := (hsin ε hε (hεr.trans hr1) u h (hu.trans hr1) ⟨hh.1, hh.2.trans hr1⟩).1
  let T := |u| + ε + h
  have hT : 0 < T := by dsimp [T]; linarith [abs_nonneg u, hh.1]
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hTle : T ≤ 4 := by dsimp [T]; linarith [hh.2]
  have hsTle : Real.sqrt T ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [hTle]⟩
  have hF : 0 < Real.sqrt (|u| + ε) := Real.sqrt_pos.mpr (by linarith [abs_nonneg u])
  have hFT : Real.sqrt (|u| + ε) ≤ Real.sqrt T := Real.sqrt_le_sqrt (by dsimp [T]; linarith [hh.1])
  have hsnum : ‖Complex.sin (((-b + u : ℝ) : ℂ) - Complex.I * (h : ℂ))‖ ≤ Real.exp 1 :=
    (complex_sin_contour_norm_le (-b + u) h hh.1).trans (Real.exp_le_exp.mpr (hh.2.trans hrone))
  have hratio :
      ‖Complex.sin (((-b + u : ℝ) : ℂ) - Complex.I * (h : ℂ)) /
        Complex.sin (upperPhysicalPhase (isotropicBranchDispersion α b ε u h))‖ ≤
        Real.exp 1 / (c * Real.sqrt T) := by
    rw [norm_div]
    exact div_le_div₀ (Real.exp_pos 1).le hsnum (mul_pos hc hsT) hlo
  have hbound : ‖branchCoordinateSlope α b ε h u‖ ≤ C / Real.sqrt T := by
    apply (norm_sub_le _ _).trans
    rw [norm_one]
    apply (add_le_add le_rfl hratio).trans
    have he : 1 + Real.exp 1 / (c * Real.sqrt T) =
        (Real.sqrt T + Real.exp 1 / c) / Real.sqrt T := by
      field_simp
    rw [he]
    exact div_le_div_of_nonneg_right (by dsimp [C]; linarith only [hsTle]) hsT.le
  exact hbound.trans (div_le_div_of_nonneg_left (by dsimp [C]; positivity) hF hFT)

end IsingBulk.AnisoF002.Isotropic
