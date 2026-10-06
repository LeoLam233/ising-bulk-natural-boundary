import IsingBulk.First.ShapePeriodTheorem

/-! Exact post-mean shape rescaling. The amplitude and denominator below are
functions on the genuine constrained hyperplane; no physical estimate is built
into their definitions. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set

/-- A post-mean-residue shape density with its squared Vandermonde retained. -/
def localShapeQuotient {n : ℕ} (k : ℕ) (A D : ShapeSpace n → ℂ)
    (x : ShapeSpace n) : ℂ :=
  (shapeVandermondeSq x : ℂ) * A x / (D x)^(k+1)

/-- The exact rescaled integrand with the quadratic scale divided out of D. -/
def rescaledShapeQuotient {n : ℕ} (k : ℕ) (A D : ShapeSpace n → ℂ)
    (lam : ℝ) (x : ShapeSpace n) : ℂ :=
  (shapeVandermondeSq x : ℂ) * A (lam • x) /
    (D (lam • x) / (lam : ℂ)^2)^(k+1)

theorem localShapeQuotient_scale {n k : ℕ}
    (hdegree : n-1+(n+1)*n = 2*k) (hn : 1 ≤ n)
    (A D : ShapeSpace n → ℂ) (lam : ℝ) (x : ShapeSpace n) :
    (lam^(n+1)) • localShapeQuotient k A D (lam • x) =
      rescaledShapeQuotient k A D lam x := by
  have hexp : n+1+(n+1)*n = 2*(k+1) := by omega
  simp only [localShapeQuotient, rescaledShapeQuotient, shapeVandermondeSq_homogeneous,
    Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow]
  rw [div_pow, div_div_eq_mul_div]
  have hp : (lam : ℂ)^(n+1) * (lam : ℂ)^((n+1)*n) = ((lam : ℂ)^2)^(k+1) := by
    rw [← pow_add, hexp, pow_mul]
  linear_combination (shapeVandermondeSq x : ℂ) * A (lam • x) /
    D (lam • x)^(k+1) * hp

/-- The square-root prefactor cancels exactly after the constrained change of
variables. This acts only on the shape integral after mean integration. -/
theorem integral_localShapeQuotient_rescale {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) (A D : ShapeSpace n → ℂ)
    {lam : ℝ} (hlam : 0 < lam) :
    lam • (∫ x : ShapeSpace n, localShapeQuotient k A D x) =
      ∫ x : ShapeSpace n, rescaledShapeQuotient k A D lam x := by
  have hs := (volume : Measure (ShapeSpace n)).integral_comp_smul_of_nonneg
    (localShapeQuotient k A D) lam (hR := hlam.le)
  rw [finrank_shapeSpace] at hs
  have hchange : (∫ x : ShapeSpace n, localShapeQuotient k A D x) =
      lam^n • ∫ x : ShapeSpace n, localShapeQuotient k A D (lam • x) := by
    rw [hs, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hlam.ne'), one_smul]
  rw [hchange, smul_smul, ← pow_succ', ← integral_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => localShapeQuotient_scale hdegree hn A D lam x

end
end IsingBulk.First
