import IsingBulk.AnisoF002.Geometry.EndpointSide
import IsingBulk.AnisoF002.C03.RegularDensity

/-!
# The two endpoint charts on both sides of the physical boundaries

F002 proposition 2.4.  The division-free defect proves strictness for every
nonzero real part.  The second direction is the exact axis exchange
`(lam,z) ↦ (lam⁻¹,lam*z)`.  No historical chart theorem is used.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic Set Filter
open scoped Topology

theorem spectralS_ne_zero_of_re_ne_zero {z : ℂ} (hx : z.re ≠ 0) :
    spectralS z ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  change (Complex.sinh z).re = 0 at hre
  change (Complex.sinh z).im = 0 at him
  rw [complex_sinh_re] at hre
  rw [complex_sinh_im] at him
  have hcos : Real.cos z.im = 0 :=
    (mul_eq_zero.mp hre).resolve_left (Real.sinh_ne_zero.mpr hx)
  have hsin : Real.sin z.im = 0 :=
    (mul_eq_zero.mp him).resolve_left (ne_of_gt (Real.cosh_pos z.re))
  have hh := Real.cos_sq_add_sin_sq z.im
  rw [hcos, hsin] at hh
  norm_num at hh

theorem regular_first_endpoint_exists_all_re {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0)
    (hedge : geometryF1 lam z.re z.im = 0)
    (hsecond : geometryF2 lam z.re z.im ≠ 0) :
    spectralDetF002 lam z ≠ 0 ∧
    ∃ u e : ℝ, |u| < 1 ∧ (e = 1 ∨ e = -1) ∧
      spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ) := by
  obtain ⟨u, e, _, he, hinc⟩ := first_endpoint_realization hedge
  have hc := cramer_numerator_of_unsquared_incidence hinc
  rw [numerator_formula, determinant_formula] at hc
  have hH := Real.sinh_ne_zero.mpr (mul_ne_zero (ne_of_gt hlam) hx)
  have hh := regular_edge_strict_coordinate _ _ _ _ _ _ _ _ u
    (Real.cosh_sq_sub_sinh_sq z.re) (Real.cosh_sq_sub_sinh_sq (lam * z.re))
    (Real.cos_sq_add_sin_sq z.im) (Real.cos_sq_add_sin_sq (lam * z.im))
    hedge hc hH hsecond
  rw [← determinant_formula] at hh
  exact ⟨hh.1, u, e, hh.2, he, hinc⟩

theorem endpoint_affine_factor_ne_zero_all_re {lam : ℝ} {z : ℂ} {u e : ℝ}
    (hlam : 0 < lam) (hx : z.re ≠ 0)
    (hu : u ∈ Icc (-1 : ℝ) 1) (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ)) :
    (e : ℂ) + (lam : ℂ) * spectralS z ≠ 0 := by
  have hs := first_endpoint_signed_equation hu he hinc
  have hC := Real.cosh_pos (lam * z.re)
  have hprod : 0 < Real.sinh z.re * Real.sinh (lam * z.re) := by
    rcases lt_or_gt_of_ne hx with hx | hx
    · exact mul_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hx)
        (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg hlam hx))
    · exact mul_pos (Real.sinh_pos_iff.mpr hx)
        (Real.sinh_pos_iff.mpr (mul_pos hlam hx))
  have hsign : 0 < Real.sinh z.re * (e * Real.cos z.im) := by
    apply (mul_pos_iff_of_pos_left hC).mp
    calc
      0 < Real.cosh z.re * (Real.sinh z.re * Real.sinh (lam * z.re)) :=
        mul_pos (Real.cosh_pos _) hprod
      _ = Real.cosh (lam * z.re) * (Real.sinh z.re * (e * Real.cos z.im)) := by
        linear_combination Real.sinh z.re * hs
  intro hz
  have hre := congrArg Complex.re hz
  change ((e : ℂ) + (lam : ℂ) * Complex.sinh z).re = 0 at hre
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    complex_sinh_re, zero_mul, sub_zero] at hre
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  have hzero : 1 + lam * (Real.sinh z.re * (e * Real.cos z.im)) = 0 := by
    linear_combination e * hre - he2
  have hp := mul_pos hlam hsign
  linarith

theorem edgeDerivative_ne_zero_all_re {lam : ℝ} {z : ℂ} {u e : ℝ}
    (hlam : 0 < lam) (hx : z.re ≠ 0) (hu : |u| < 1) (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ)) :
    edgeDerivativeF002 lam e z ≠ 0 := by
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  have hu2 : u ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one u).2 hu
  have huC : (u : ℂ) ^ 2 - 1 ≠ 0 := by
    have huR : u ^ 2 - 1 ≠ 0 := by linarith
    exact_mod_cast huR
  have hK : endpointKF002 lam e z ≠ 0 := by
    intro hK
    have hh := endpointK_square he hinc
    rw [hK, zero_pow (by omega)] at hh
    exact (mul_ne_zero (pow_ne_zero 2 hS) huC) hh.symm
  have hui : u ∈ Icc (-1 : ℝ) 1 := ⟨(abs_lt.mp hu).1.le, (abs_lt.mp hu).2.le⟩
  exact div_ne_zero
    (mul_ne_zero hK (endpoint_affine_factor_ne_zero_all_re hlam hx hui he hinc))
    (pow_ne_zero 2 hS)

theorem regular_first_endpoint_chart_all_re {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0)
    (hedge : geometryF1 lam z.re z.im = 0)
    (hsecond : geometryF2 lam z.re z.im ≠ 0) :
    ∃ u e : ℝ, |u| < 1 ∧ (e = 1 ∨ e = -1) ∧
      spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ) ∧
      spectralDetF002 lam z ≠ 0 ∧
      edgeCoordinateF002 lam e z = (u : ℂ) ∧
      HasDerivAt (edgeCoordinateF002 lam e) (edgeDerivativeF002 lam e z) z ∧
      edgeDerivativeF002 lam e z ≠ 0 ∧
      (∀ᶠ w in 𝓝 z, w ∉ spectralSetF002 lam ↔
        0 < e * spectralDetF002 lam w * (edgeCoordinateF002 lam e w).im) := by
  obtain ⟨hdet, u, e, hu, he, hinc⟩ :=
    regular_first_endpoint_exists_all_re hlam hx hedge hsecond
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  refine ⟨u, e, hu, he, hinc, hdet, edgeCoordinate_eq_of_incidence hS hinc,
    edgeCoordinate_hasDerivAt he hS, edgeDerivative_ne_zero_all_re hlam hx hu he hinc, ?_⟩
  filter_upwards [eventually_signed_side_of_incidence hdet hS hu he hinc] with w hw
  exact hw.not.trans not_le

theorem axis_swap_complex {lam : ℝ} (hlam : lam ≠ 0) (z : ℂ) :
    ((lam⁻¹ : ℝ) : ℂ) * ((lam : ℂ) * z) = z := by
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam,
    Complex.ofReal_one, one_mul]

theorem axis_swap_first_factor {lam : ℝ} (hlam : lam ≠ 0) (z : ℂ) :
    geometryF1 lam⁻¹ ((lam : ℂ) * z).re ((lam : ℂ) * z).im =
      geometryF2 lam z.re z.im := by
  have hswap : lam⁻¹ * (lam * z.re) = z.re := by field_simp [hlam]
  delta geometryF1 geometryF2
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, hswap]
  ring

theorem axis_swap_second_factor {lam : ℝ} (hlam : lam ≠ 0) (z : ℂ) :
    geometryF2 lam⁻¹ ((lam : ℂ) * z).re ((lam : ℂ) * z).im =
      geometryF1 lam z.re z.im := by
  have hswapR : lam⁻¹ * (lam * z.re) = z.re := by field_simp [hlam]
  have hswapI : lam⁻¹ * (lam * z.im) = z.im := by field_simp [hlam]
  delta geometryF1 geometryF2
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, hswapR, hswapI]
  ring

theorem axis_swap_spectral_set {lam : ℝ} (hlam : lam ≠ 0) (z : ℂ) :
    (lam : ℂ) * z ∈ spectralSetF002 lam⁻¹ ↔ z ∈ spectralSetF002 lam := by
  have hh := axis_swap_complex hlam z
  change (∃ u ∈ Icc (-1 : ℝ) 1, ∃ v ∈ Icc (-1 : ℝ) 1,
      spectralA lam⁻¹ ((lam : ℂ) * z) = spectralS ((lam : ℂ) * z) * (u : ℂ) +
        spectralT lam⁻¹ ((lam : ℂ) * z) * (v : ℂ)) ↔ _
  delta spectralSetF002 spectralA spectralS spectralT
  rw [hh]
  constructor <;> rintro ⟨u, hu, v, hv, hi⟩
  · exact ⟨v, hv, u, hu, by simpa only [mul_comm, add_comm] using hi⟩
  · exact ⟨v, hv, u, hu, by simpa only [mul_comm, add_comm] using hi⟩

def secondEdgeCoordinateF002 (lam e : ℝ) (z : ℂ) : ℂ :=
  (spectralA lam z - spectralS z * (e : ℂ)) / spectralT lam z

theorem secondEdgeCoordinate_eq_swap {lam : ℝ} (hlam : lam ≠ 0) (e : ℝ) (z : ℂ) :
    secondEdgeCoordinateF002 lam e z = edgeCoordinateF002 lam⁻¹ e ((lam : ℂ) * z) := by
  delta secondEdgeCoordinateF002 edgeCoordinateF002 spectralA spectralS spectralT
  rw [axis_swap_complex hlam]
  rw [mul_comm (Complex.cosh ((lam : ℂ) * z)) (Complex.cosh z)]

theorem axis_swap_determinant {lam : ℝ} (hlam : lam ≠ 0) (z : ℂ) :
    spectralDetF002 lam⁻¹ ((lam : ℂ) * z) = -spectralDetF002 lam z := by
  delta spectralDetF002 spectralS spectralT
  rw [axis_swap_complex hlam]
  ring

theorem regular_second_endpoint_chart_all_re {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0)
    (hedge : geometryF2 lam z.re z.im = 0)
    (hfirst : geometryF1 lam z.re z.im ≠ 0) :
    ∃ v e : ℝ, ∃ d : ℂ, |v| < 1 ∧ (e = 1 ∨ e = -1) ∧
      spectralA lam z = spectralS z * (e : ℂ) + spectralT lam z * (v : ℂ) ∧
      spectralDetF002 lam z ≠ 0 ∧ secondEdgeCoordinateF002 lam e z = (v : ℂ) ∧
      HasDerivAt (secondEdgeCoordinateF002 lam e) d z ∧ d ≠ 0 ∧
      (∀ᶠ w in 𝓝 z, w ∉ spectralSetF002 lam ↔
        0 < -e * spectralDetF002 lam w * (secondEdgeCoordinateF002 lam e w).im) := by
  have h0 := ne_of_gt hlam
  have hx' : ((lam : ℂ) * z).re ≠ 0 := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] using mul_ne_zero h0 hx
  have hedge' : geometryF1 lam⁻¹ ((lam : ℂ) * z).re ((lam : ℂ) * z).im = 0 := by
    rwa [axis_swap_first_factor h0]
  have hfirst' : geometryF2 lam⁻¹ ((lam : ℂ) * z).re ((lam : ℂ) * z).im ≠ 0 := by
    rwa [axis_swap_second_factor h0]
  obtain ⟨v, e, hv, he, hi, hdet, hc, hd, hd0, hs⟩ :=
    regular_first_endpoint_chart_all_re (inv_pos.mpr hlam) hx' hedge' hfirst'
  refine ⟨v, e, edgeDerivativeF002 lam⁻¹ e ((lam : ℂ) * z) * (lam : ℂ),
    hv, he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · delta spectralA spectralS spectralT at hi ⊢
    rw [axis_swap_complex h0] at hi
    simpa only [mul_comm, add_comm] using hi
  · rw [axis_swap_determinant h0, neg_ne_zero] at hdet
    exact hdet
  · rwa [secondEdgeCoordinate_eq_swap h0]
  · have hh := hd.comp z (hasDerivAt_const_mul (lam : ℂ))
    simpa only [Function.comp_def, ← secondEdgeCoordinate_eq_swap h0] using hh
  · exact mul_ne_zero hd0 (Complex.ofReal_ne_zero.mpr h0)
  · have hcont : ContinuousAt (fun w : ℂ => (lam : ℂ) * w) z :=
      continuousAt_const.mul continuousAt_id
    filter_upwards [hcont.eventually hs] with w hw
    rw [axis_swap_spectral_set h0, axis_swap_determinant h0,
      ← secondEdgeCoordinate_eq_swap h0] at hw
    simpa only [mul_neg, neg_mul] using hw

end
end IsingBulk.AnisoF002.Geometry
