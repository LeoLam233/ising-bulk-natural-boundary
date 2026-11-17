import IsingBulk.AnisoF002.Geometry.EndpointConverse

/-!
# The actual regular endpoint coordinate is nonramified

F002 `eq:endpointrepresentation`, `eq:endpoint-defect`, and the derivative
calculation immediately before `prop:regular_dense`.  We differentiate the
displayed physical quotient `gε = (A - ε T) / S` directly.  Its numerator
factors through the same `K` used by the paper's endpoint-defect argument.
No historical edge-coordinate or local inverse theorem is invoked.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic

def edgeCoordinateF002 (lam e : ℝ) (z : ℂ) : ℂ :=
  (spectralA lam z - spectralT lam z * (e : ℂ)) / spectralS z

def endpointKF002 (lam e : ℝ) (z : ℂ) : ℂ :=
  Complex.cosh z * spectralT lam z - (e : ℂ) * Complex.cosh ((lam : ℂ) * z)

def edgeDerivativeF002 (lam e : ℝ) (z : ℂ) : ℂ :=
  endpointKF002 lam e z * ((e : ℂ) + (lam : ℂ) * spectralS z) / spectralS z ^ 2

theorem spectralS_ne_zero_of_re_pos {z : ℂ} (hx : 0 < z.re) : spectralS z ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  change (Complex.sinh z).re = 0 at hre
  change (Complex.sinh z).im = 0 at him
  rw [complex_sinh_re] at hre
  rw [complex_sinh_im] at him
  have hcos : Real.cos z.im = 0 :=
    (mul_eq_zero.mp hre).resolve_left (ne_of_gt (Real.sinh_pos_iff.mpr hx))
  have hsin : Real.sin z.im = 0 :=
    (mul_eq_zero.mp him).resolve_left (ne_of_gt (Real.cosh_pos z.re))
  have hh := Real.cos_sq_add_sin_sq z.im
  rw [hcos, hsin] at hh
  norm_num at hh

theorem first_endpoint_signed_equation {lam : ℝ} {z : ℂ} {u e : ℝ}
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ)) :
    Real.cosh z.re * Real.sinh (lam * z.re) =
      e * Real.cosh (lam * z.re) * Real.cos z.im := by
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  have hre := congrArg Complex.re hinc
  have him := congrArg Complex.im hinc
  dsimp only [spectralA, spectralS, spectralT] at hre him
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    zero_add, add_zero, complex_cosh_re, complex_cosh_im, complex_sinh_re,
    complex_sinh_im] at hre him
  exact endpoint_signed_equation_of_incidence
    (Real.sinh z.re) (Real.cosh z.re)
    (Real.sinh (lam * z.re)) (Real.cosh (lam * z.re))
    (Real.cos z.im) (Real.sin z.im) (Real.cos (lam * z.im)) (Real.sin (lam * z.im))
    e u (Real.cosh_sq_sub_sinh_sq z.re) (Real.cosh_sq_sub_sinh_sq (lam * z.re))
    (Real.cos_sq_add_sin_sq z.im) (Real.cos_sq_add_sin_sq (lam * z.im)) he2 hu
    (by convert hre using 1 <;> ring) (by convert him using 1 <;> ring)

theorem endpointK_square {lam : ℝ} {z : ℂ} {u e : ℝ}
    (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ)) :
    endpointKF002 lam e z ^ 2 = spectralS z ^ 2 * ((u : ℂ) ^ 2 - 1) := by
  have he2 : (e : ℂ) ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  have hsq : (Complex.cosh z * Complex.cosh ((lam : ℂ) * z) -
      (e : ℂ) * Complex.sinh ((lam : ℂ) * z)) ^ 2 =
      (Complex.sinh z * (u : ℂ)) ^ 2 := by
    have hi : Complex.cosh z * Complex.cosh ((lam : ℂ) * z) -
        (e : ℂ) * Complex.sinh ((lam : ℂ) * z) = Complex.sinh z * (u : ℂ) := by
      delta spectralA spectralS spectralT at hinc
      linear_combination hinc
    rw [hi]
  delta endpointKF002 spectralS spectralT
  linear_combination hsq - (Complex.cosh z ^ 2 - (e : ℂ) ^ 2) *
    Complex.cosh_sq_sub_sinh_sq ((lam : ℂ) * z) -
    Complex.cosh_sq_sub_sinh_sq z + he2

theorem edgeCoordinate_eq_of_incidence {lam : ℝ} {z : ℂ} {u e : ℝ}
    (hS : spectralS z ≠ 0)
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ)) :
    edgeCoordinateF002 lam e z = (u : ℂ) := by
  unfold edgeCoordinateF002
  apply (div_eq_iff hS).2
  rw [hinc]
  ring

theorem edgeCoordinate_hasDerivAt {lam e : ℝ} {z : ℂ}
    (he : e = 1 ∨ e = -1) (hS : spectralS z ≠ 0) :
    HasDerivAt (edgeCoordinateF002 lam e) (edgeDerivativeF002 lam e z) z := by
  have he2 : (e : ℂ) ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  have hs : HasDerivAt spectralS (Complex.cosh z) z := Complex.hasDerivAt_sinh z
  have hlin : HasDerivAt (fun w : ℂ => (lam : ℂ) * w) (lam : ℂ) z :=
    hasDerivAt_const_mul (lam : ℂ)
  have ht : HasDerivAt (spectralT lam)
      (Complex.cosh ((lam : ℂ) * z) * (lam : ℂ)) z :=
    (Complex.hasDerivAt_sinh _).comp z hlin
  have hc : HasDerivAt (fun w : ℂ => Complex.cosh ((lam : ℂ) * w))
      (Complex.sinh ((lam : ℂ) * z) * (lam : ℂ)) z :=
    (Complex.hasDerivAt_cosh _).comp z hlin
  have hd := (((Complex.hasDerivAt_cosh z).mul hc).sub (ht.mul_const (e : ℂ))).div hs hS
  convert hd using 1
  · rfl
  · delta edgeDerivativeF002 endpointKF002 spectralS spectralT
    simp only [Pi.mul_apply, Pi.sub_apply]
    congr 1
    linear_combination Complex.cosh ((lam : ℂ) * z) *
      Complex.cosh_sq_sub_sinh_sq z - Complex.cosh ((lam : ℂ) * z) * he2

theorem endpoint_affine_factor_ne_zero {lam : ℝ} {z : ℂ} {u e : ℝ}
    (hlam : 0 < lam) (hx : 0 < z.re)
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ)) :
    (e : ℂ) + (lam : ℂ) * spectralS z ≠ 0 := by
  have hs := first_endpoint_signed_equation hu he hinc
  have hC : 0 < Real.cosh (lam * z.re) := Real.cosh_pos _
  have hH : 0 < Real.sinh (lam * z.re) := Real.sinh_pos_iff.mpr (mul_pos hlam hx)
  have hh : 0 < Real.sinh z.re := Real.sinh_pos_iff.mpr hx
  have hsign : 0 < e * Real.cos z.im := by
    have hp := mul_pos (Real.cosh_pos z.re) hH
    nlinarith
  intro hz
  have hre := congrArg Complex.re hz
  change ((e : ℂ) + (lam : ℂ) * Complex.sinh z).re = 0 at hre
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    complex_sinh_re, zero_mul, sub_zero] at hre
  have he2 : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  have hzero : 1 + lam * Real.sinh z.re * (e * Real.cos z.im) = 0 := by
    linear_combination e * hre - he2
  have hp : 0 < 1 + lam * Real.sinh z.re * (e * Real.cos z.im) := by positivity
  exact (ne_of_gt hp) hzero

theorem edgeDerivative_ne_zero {lam : ℝ} {z : ℂ} {u e : ℝ}
    (hlam : 0 < lam) (hx : 0 < z.re) (hu : |u| < 1) (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (e : ℂ)) :
    edgeDerivativeF002 lam e z ≠ 0 := by
  have hS := spectralS_ne_zero_of_re_pos hx
  have hu2 : u ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one u).2 hu
  have huC : (u : ℂ) ^ 2 - 1 ≠ 0 := by
    have huR : u ^ 2 - 1 ≠ 0 := by linarith
    exact_mod_cast huR
  have hK : endpointKF002 lam e z ≠ 0 := by
    intro hK
    have hh := endpointK_square he hinc
    rw [hK, zero_pow (by omega)] at hh
    exact (mul_ne_zero (pow_ne_zero 2 hS) huC) hh.symm
  have hui : u ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨(abs_lt.mp hu).1.le, (abs_lt.mp hu).2.le⟩
  exact div_ne_zero (mul_ne_zero hK (endpoint_affine_factor_ne_zero hlam hx hui he hinc))
    (pow_ne_zero 2 hS)

/-- A real first-factor regular edge supplies its actual nonramified
holomorphic coordinate, with no extra regularity premise. -/
theorem regular_first_edge_coordinate {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : 0 < z.re)
    (hedge : geometryF1 lam z.re z.im = 0)
    (hsecond : geometryF2 lam z.re z.im ≠ 0) :
    ∃ u e : ℝ, |u| < 1 ∧ (e = 1 ∨ e = -1) ∧
      edgeCoordinateF002 lam e z = (u : ℂ) ∧
      HasDerivAt (edgeCoordinateF002 lam e) (edgeDerivativeF002 lam e z) z ∧
      edgeDerivativeF002 lam e z ≠ 0 := by
  obtain ⟨_, u, e, hu, he, hinc⟩ :=
    regular_first_endpoint_exists hlam hx hedge hsecond
  have hS := spectralS_ne_zero_of_re_pos hx
  exact ⟨u, e, hu, he, edgeCoordinate_eq_of_incidence hS hinc,
    edgeCoordinate_hasDerivAt he hS, edgeDerivative_ne_zero hlam hx hu he hinc⟩

end
end IsingBulk.AnisoF002.Geometry
