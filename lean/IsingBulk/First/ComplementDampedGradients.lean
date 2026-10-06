import IsingBulk.First.ComplementGradients
import IsingBulk.First.ComplementSeparation

/-! Actual damped exponential factors and their real directional gradients. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

/-- The scalar exponent attached to each actual damped reciprocal factor. -/
def singularFactorExponent {N : ℕ} (r : ℝ) (s : ℂ) (x y : Fin N → ℂ)
    (e : DoubleAngularVector N) : SingularFactorIndex N → ℝ → ℂ
  | .inl false, t => (∏ i, angularCurve ((r : ℂ) * x i) (e.1 i) t) - 1
  | .inl true, t => (∏ i, angularCurve ((r : ℂ) * y i) (e.2 i) t) - 1
  | .inr (.inl (false, i, j)), t =>
      angularCurve ((r : ℂ) * x i) (e.1 i) t * angularCurve ((r : ℂ) * x j) (e.1 j) t - 1
  | .inr (.inl (true, i, j)), t =>
      angularCurve ((r : ℂ) * y i) (e.2 i) t * angularCurve ((r : ℂ) * y j) (e.2 j) t - 1
  | .inr (.inr i), t => Complex.I * dispersion
      (angularCurve ((r : ℂ) * x i) (e.1 i) t)
      (angularCurve ((r : ℂ) * y i) (e.2 i) t) s

/-- General trace derivative before restricting to the unit circle. -/
theorem angular_trace_general_hasDerivAt {z : ℂ} (hz : z ≠ 0) (a : ℝ) :
    HasDerivAt (fun t => (angularCurve z a t + (angularCurve z a t)⁻¹) / 2)
      ((z - z⁻¹) * (a : ℂ) * Complex.I / 2) 0 := by
  have h := angularCurve_hasDerivAt z a
  have hi : HasDerivAt (fun t => (angularCurve z a t)⁻¹)
      (-z⁻¹ * (a : ℂ) * Complex.I) 0 := by
    convert h.inv (by simpa using hz) using 1
    simp only [angularCurve_zero]
    field_simp
  convert (h.add hi).div_const (2 : ℂ) using 1
  ring

/-- No limiting linearization is used in the dispersion exponent derivative. -/
theorem dispersion_exponent_general_hasDerivAt {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (s : ℂ) (a b : ℝ) :
    HasDerivAt (fun t => Complex.I * dispersion (angularCurve x a t) (angularCurve y b t) s)
      (((a : ℂ) * (x - x⁻¹) + (b : ℂ) * (y - y⁻¹)) / 2) 0 := by
  have h := (((angular_trace_general_hasDerivAt hx a).const_sub (sourceS s)).sub
    (angular_trace_general_hasDerivAt hy b)).const_mul Complex.I
  convert h using 1
  · rfl
  · ring_nf
    simp [Complex.I_sq]
    ring

/-- Product exponent derivative with its full actual product coefficient. -/
theorem product_exponent_general_hasDerivAt {N : ℕ} (x : Fin N → ℂ) (e : Fin N → ℝ) :
    HasDerivAt (fun t => (∏ i, angularCurve (x i) (e i) t) - 1)
      ((∏ i, x i) * ((∑ i, e i : ℝ) : ℂ) * Complex.I) 0 := by
  convert (angularCurve_hasDerivAt (∏ i, x i) (∑ i, e i)).sub_const 1 using 1
  funext t
  rw [product_angularCurve]
  rfl

/-- Pair exponent derivative with its full actual product coefficient. -/
theorem pair_exponent_general_hasDerivAt (x y : ℂ) (a b : ℝ) :
    HasDerivAt (fun t => angularCurve x a t * angularCurve y b t - 1)
      ((x * y) * ((a + b : ℝ) : ℂ) * Complex.I) 0 := by
  convert ((angularCurve_hasDerivAt x a).mul (angularCurve_hasDerivAt y b)).sub_const 1 using 1
  simp only [angularCurve_zero]
  push_cast
  ring

/-- Imaginary component of a reciprocal damped unit coordinate. -/
theorem damped_inverse_im {x : ℂ} (hx : ‖x‖ = 1) (r : ℝ) :
    (((r : ℂ) * x)⁻¹).im = -r⁻¹ * x.im := by
  rw [mul_inv, Complex.inv_eq_conj hx, ← Complex.ofReal_inv]
  simp

/-- The actual product imaginary gradient agrees with the damped vector. -/
theorem damped_product_exponent_im_hasDerivAt {N : ℕ} (r : ℝ)
    (x : Fin N → ℂ) (e : Fin N → ℝ) :
    HasDerivAt (fun t => ((∏ i, angularCurve ((r : ℂ) * x i) (e i) t) - 1).im)
      ((r ^ N * (∏ i, x i).re) * ∑ i, e i) 0 := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0
    (product_exponent_general_hasDerivAt (fun i => (r : ℂ) * x i) e)
  convert h using 1
  · rfl
  · simp [Finset.prod_mul_distrib, Complex.mul_re, Complex.mul_im]
    simp [← Complex.ofReal_pow, mul_comm]

/-- The actual pair imaginary gradient agrees with the damped vector. -/
theorem damped_pair_exponent_im_hasDerivAt (r : ℝ) (x y : ℂ) (a b : ℝ) :
    HasDerivAt (fun t => (angularCurve ((r : ℂ) * x) a t *
      angularCurve ((r : ℂ) * y) b t - 1).im)
      ((r ^ 2 * (x * y).re) * (a + b)) 0 := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0
    (pair_exponent_general_hasDerivAt ((r : ℂ) * x) ((r : ℂ) * y) a b)
  convert h using 1
  · rfl
  · simp [Complex.mul_re, Complex.mul_im]
    ring_nf
    simp

/-- The actual damped dispersion imaginary gradient has the stated cosh factor. -/
theorem damped_dispersion_exponent_im_hasDerivAt {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (r : ℝ) (hr : r ≠ 0) (s : ℂ) (a b : ℝ) :
    HasDerivAt (fun t => (Complex.I * dispersion
      (angularCurve ((r : ℂ) * x) a t) (angularCurve ((r : ℂ) * y) b t) s).im)
      (((r + r⁻¹) / 2) * (a * x.im + b * y.im)) 0 := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0
    (dispersion_exponent_general_hasDerivAt
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) hx0)
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) hy0) s a b)
  convert h using 1
  · rfl
  · simp only [Complex.imCLM_apply, Complex.div_ofNat_im, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      zero_mul, add_zero, damped_inverse_im hx, damped_inverse_im hy]
    ring

/-- Every damped vector used in separation is the actual imaginary directional
exponent derivative. This closes the vector-formula identification. -/
theorem singularFactorExponent_im_hasDerivAt {N : ℕ} (r : ℝ) (hr : r ≠ 0) (s : ℂ)
    (x y : Fin N → ℂ) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (e : DoubleAngularVector N) (f : SingularFactorIndex N) :
    HasDerivAt (fun t => (singularFactorExponent r s x y e f t).im)
      (angularDot e (dampedSingularVector r x y f)) 0 := by
  classical
  rcases f with b | (⟨b, i, j⟩ | i)
  · cases b
    · simpa [singularFactorExponent, dampedSingularVector, angularDot, Finset.sum_mul,
        mul_comm] using damped_product_exponent_im_hasDerivAt r x e.1
    · simpa [singularFactorExponent, dampedSingularVector, angularDot, Finset.sum_mul,
        mul_comm] using damped_product_exponent_im_hasDerivAt r y e.2
  · cases b
    · simpa [singularFactorExponent, dampedSingularVector, angularDot, Pi.single_apply,
        mul_add, add_mul, Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc] using
        damped_pair_exponent_im_hasDerivAt r (x i) (x j) (e.1 i) (e.1 j)
    · simpa [singularFactorExponent, dampedSingularVector, angularDot, Pi.single_apply,
        mul_add, add_mul, Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc] using
        damped_pair_exponent_im_hasDerivAt r (y i) (y j) (e.2 i) (e.2 j)
  · simpa [singularFactorExponent, dampedSingularVector, angularDot, Pi.single_apply,
      mul_add, mul_comm, mul_left_comm, mul_assoc] using
      damped_dispersion_exponent_im_hasDerivAt (hx i) (hy i) r hr s (e.1 i) (e.2 i)

end
end IsingBulk.First
