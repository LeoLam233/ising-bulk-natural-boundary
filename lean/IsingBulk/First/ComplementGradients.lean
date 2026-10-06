import IsingBulk.First.ComplementVectors
import IsingBulk.First.ContourDefinitions
import Mathlib.Analysis.Complex.RealDeriv

/-! Directional derivatives of the actual source factors on the limiting torus. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

/-- Move a source coordinate in a real angular direction. -/
def angularCurve (z : ℂ) (a t : ℝ) : ℂ :=
  z * Complex.exp ((t : ℂ) * (a : ℂ) * Complex.I)

@[simp] theorem angularCurve_zero (z : ℂ) (a : ℝ) : angularCurve z a 0 = z := by
  simp [angularCurve]

theorem angularCurve_hasDerivAt (z : ℂ) (a : ℝ) :
    HasDerivAt (angularCurve z a) (z * (a : ℂ) * Complex.I) 0 := by
  have h := (((((hasDerivAt_id (0 : ℂ)).mul_const (a : ℂ)).mul_const Complex.I).cexp).const_mul z).comp_ofReal
  unfold angularCurve
  simpa [mul_assoc] using h

/-- The actual dispersion derivative, with no linearized substitute. -/
theorem angular_trace_hasDerivAt {z : ℂ} (hz : ‖z‖ = 1) (a : ℝ) :
    HasDerivAt (fun t => (angularCurve z a t + (angularCurve z a t)⁻¹) / 2)
      (-((a * z.im : ℝ) : ℂ)) 0 := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have h := angularCurve_hasDerivAt z a
  have hi : HasDerivAt (fun t => (angularCurve z a t)⁻¹)
      (-z⁻¹ * (a : ℂ) * Complex.I) 0 := by
    convert h.inv (by simpa using hz0) using 1
    simp only [angularCurve_zero]
    field_simp
  have ht := (h.add hi).div_const (2 : ℂ)
  convert ht using 1
  rw [Complex.inv_eq_conj hz]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The dispersion exponent is iD, hence its limiting derivative has the
positive source vector entries Im x and Im y. -/
theorem dispersion_exponent_hasDerivAt {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (s : ℂ) (a b : ℝ) :
    HasDerivAt (fun t => Complex.I * dispersion (angularCurve x a t) (angularCurve y b t) s)
      (Complex.I * ((a * x.im + b * y.im : ℝ) : ℂ)) 0 := by
  have h := (((angular_trace_hasDerivAt hx a).const_sub (sourceS s)).sub
    (angular_trace_hasDerivAt hy b)).const_mul Complex.I
  convert h using 1 <;> simp [dispersion]

/-- Finite products of actual angular curves retain their exact total phase. -/
theorem product_angularCurve {N : ℕ} (x : Fin N → ℂ) (e : Fin N → ℝ) (t : ℝ) :
    (∏ i, angularCurve (x i) (e i) t) =
      (∏ i, x i) * Complex.exp ((t : ℂ) * ((∑ i, e i : ℝ) : ℂ) * Complex.I) := by
  unfold angularCurve
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

/-- The negative product denominator has the all-ones vector at an active point. -/
theorem product_exponent_hasDerivAt {N : ℕ} {x : Fin N → ℂ}
    (hX : ∏ i, x i = 1) (e : Fin N → ℝ) :
    HasDerivAt (fun t => (∏ i, angularCurve (x i) (e i) t) - 1)
      (Complex.I * ((∑ i, e i : ℝ) : ℂ)) 0 := by
  have h := (angularCurve_hasDerivAt (∏ i, x i) (∑ i, e i)).sub_const 1
  convert h using 1
  · funext t
    rw [product_angularCurve]
    rfl
  · rw [hX]
    ring

/-- The negative pair denominator has the sum of the two coordinate directions. -/
theorem pair_exponent_hasDerivAt {x y : ℂ} (hxy : x * y = 1) (a b : ℝ) :
    HasDerivAt (fun t => angularCurve x a t * angularCurve y b t - 1)
      (Complex.I * ((a + b : ℝ) : ℂ)) 0 := by
  have h := ((angularCurve_hasDerivAt x a).mul (angularCurve_hasDerivAt y b)).sub_const 1
  convert h using 1
  simp only [angularCurve_zero]
  calc
    _ = (x * y) * (a + b) * Complex.I := by rw [hxy]; push_cast; ring
    _ = _ := by ring

end
end IsingBulk.First
