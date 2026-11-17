import IsingBulk.AnisoF002.C03.IsotropicBoundaryRoot

/-!
# The actual boundary root has a genuine local holomorphic continuation

Every real dispersion x>-1 other than the branch point x=1 is covered.
On the left arc x>1 the continued root is W-sqrt(W^2-1); using the
interior formula at the real cut itself would select the wrong root.
The continuation is identified with the actual upper root on a common
open neighborhood intersected with the physical upper half-plane.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.Geometry
open scoped Topology ComplexOrder

def isotropicNonbranchLocalRoot (x : ℝ) (W : ℂ) : ℂ :=
  if x < 1 then upperEdgeRoot W else W - Complex.sqrt (W ^ 2 - 1)

theorem complex_sqrt_ofReal_nonneg_F002 {x : ℝ} (hx : 0 ≤ x) :
    Complex.sqrt (x : ℂ) = (Real.sqrt x : ℂ) := by
  simpa only [Complex.ofReal_re] using
    Complex.sqrt_of_nonneg (show (0 : ℂ) ≤ (x : ℂ) by exact_mod_cast hx)

theorem isotropicNonbranchLocalRoot_center {x : ℝ} (hx : -1 < x) (hx1 : x ≠ 1) :
    isotropicNonbranchLocalRoot x (x : ℂ) = upperBoundaryRoot x := by
  by_cases h : x < 1
  · have hsq : x ^ 2 < 1 := by nlinarith
    have hz : Real.sqrt (x ^ 2 - 1) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    rw [isotropicNonbranchLocalRoot, ite_eq_left h, upperEdgeRoot, upperBoundaryRoot, hz,
      Complex.ofReal_zero, sub_zero,
      show (1 : ℂ) - (x : ℂ) ^ 2 = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; rfl,
      complex_sqrt_ofReal_nonneg_F002 (by linarith)]
  · have hgt : 1 < x := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hx1)
    have hz : Real.sqrt (1 - x ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [isotropicNonbranchLocalRoot, ite_eq_right h, upperBoundaryRoot, hz,
      Complex.ofReal_zero, mul_zero, sub_zero,
      show (x : ℂ) ^ 2 - 1 = ((x ^ 2 - 1 : ℝ) : ℂ) by push_cast; rfl,
      complex_sqrt_ofReal_nonneg_F002 (by nlinarith)]

theorem isotropicNonbranchLocalRoot_polynomial (x : ℝ) (W : ℂ) :
    isotropicNonbranchLocalRoot x W ^ 2 - 2 * W * isotropicNonbranchLocalRoot x W + 1 = 0 := by
  by_cases h : x < 1
  · simpa only [isotropicNonbranchLocalRoot, ite_eq_left h] using upperEdgeRoot_polynomial W
  · have hs : Complex.sqrt (W ^ 2 - 1) ^ 2 = W ^ 2 - 1 := by
      simpa only [Complex.sqrt] using Complex.cpow_ofNat_inv_pow (W ^ 2 - 1) 2
    simp only [isotropicNonbranchLocalRoot, ite_eq_right h]
    linear_combination hs

theorem isotropicNonbranchLocalRoot_analyticAt {x : ℝ} (hx : -1 < x) (hx1 : x ≠ 1) :
    AnalyticAt ℂ (isotropicNonbranchLocalRoot x) (x : ℂ) := by
  by_cases h : x < 1
  · have he : isotropicNonbranchLocalRoot x = upperEdgeRoot := by
      funext W; exact ite_eq_left h
    rw [he]
    apply upperEdgeRoot_analyticAt
    exact edge_discriminant_slit (Or.inr ⟨rfl, by simpa only [Complex.ofReal_re, abs_lt] using And.intro hx h⟩)
  · have hgt : 1 < x := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hx1)
    have hs : (x : ℂ) ^ 2 - 1 ∈ Complex.slitPlane := by
      rw [show (x : ℂ) ^ 2 - 1 = ((x ^ 2 - 1 : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.ofReal_mem_slitPlane.mpr (by nlinarith)
    have hd : AnalyticAt ℂ (fun W : ℂ => W ^ 2 - 1) (x : ℂ) :=
      (analyticAt_id.pow 2).sub analyticAt_const
    have hroot : AnalyticAt ℂ (fun W : ℂ => Complex.sqrt (W ^ 2 - 1)) (x : ℂ) := by
      simpa only [Complex.sqrt] using hd.cpow (g := fun _ : ℂ => (2⁻¹ : ℂ)) analyticAt_const hs
    have he : isotropicNonbranchLocalRoot x = fun W : ℂ => W - Complex.sqrt (W ^ 2 - 1) := by
      funext W; exact ite_eq_right h
    rw [he]
    exact analyticAt_id.sub hroot

theorem upperBoundaryRoot_norm_lt_one_of_gt_one {x : ℝ} (hx : 1 < x) :
    ‖upperBoundaryRoot x‖ < 1 := by
  have hz : Real.sqrt (1 - x ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by nlinarith)
  have hs := Real.sq_sqrt (show 0 ≤ x ^ 2 - 1 by nlinarith)
  have hpos : 0 < x - Real.sqrt (x ^ 2 - 1) := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 - 1)]
  have hlt : x - Real.sqrt (x ^ 2 - 1) < 1 := by
    nlinarith [Real.sqrt_nonneg (x ^ 2 - 1)]
  have he : upperBoundaryRoot x = ((x - Real.sqrt (x ^ 2 - 1) : ℝ) : ℂ) := by
    simp [upperBoundaryRoot, hz]
  rw [he, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  exact hlt

theorem isotropicNonbranchLocalRoot_matches_upper {x : ℝ} (hx : -1 < x) (hx1 : x ≠ 1) :
    ∀ᶠ W : ℂ in 𝓝 (x : ℂ), 0 < W.im → isotropicNonbranchLocalRoot x W = upperEdgeRoot W := by
  by_cases h : x < 1
  · exact Filter.Eventually.of_forall fun W _ => ite_eq_left h
  · have hgt : 1 < x := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hx1)
    have hnorm : ‖isotropicNonbranchLocalRoot x (x : ℂ)‖ < 1 := by
      rw [isotropicNonbranchLocalRoot_center hx hx1]
      exact upperBoundaryRoot_norm_lt_one_of_gt_one hgt
    filter_upwards [((isotropicNonbranchLocalRoot_analyticAt hx hx1).continuousAt.norm).eventually
      (Iio_mem_nhds hnorm)] with W hW
    intro him
    exact reciprocal_small_root_unique (isotropicNonbranchLocalRoot_polynomial x W)
      (upperEdgeRoot_polynomial W) hW (upperEdgeRoot_norm_lt_one him)

theorem upperBoundaryRoot_oneBody_ne_zero {x : ℝ} (hx : -1 < x) (hx1 : x ≠ 1) :
    1 - upperBoundaryRoot x ^ 2 ≠ 0 := by
  intro he
  have hp := (upperBoundaryRoot_spec x hx).1
  have heq : upperBoundaryRoot x ^ 2 = 1 := (sub_eq_zero.mp he).symm
  rcases sq_eq_one_iff.mp heq with hr | hr
  · rw [hr] at hp
    have hc : (x : ℂ) = 1 := by linear_combination -hp / 2
    exact hx1 (by exact_mod_cast hc)
  · rw [hr] at hp
    have hc : (x : ℂ) = -1 := by linear_combination hp / 2
    have hreal : x = -1 := by exact_mod_cast hc
    linarith

end
end IsingBulk.AnisoF002.Isotropic
