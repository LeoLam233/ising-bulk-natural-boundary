import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Source-serving bounds for the constrained FIRST period. These lemmas concern
its actual radial kernel and do not assume its value or nonvanishing. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate

/-- The radial majorant after the squared Vandermonde and polar Jacobian have
been combined. In the source `m = k = N^2/2 - 1`. -/
def shapeRadialMajorant (m : ℕ) (r : ℝ) : ℝ :=
  r ^ (2 * m) / (1 + r ^ 2) ^ (m + 1)

theorem shapeRadialMajorant_nonneg (m : ℕ) (r : ℝ) :
    0 ≤ shapeRadialMajorant m r := by
  unfold shapeRadialMajorant
  rw [pow_mul]
  positivity

theorem shapeRadialMajorant_le (m : ℕ) (r : ℝ) :
    shapeRadialMajorant m r ≤ (1 + r ^ 2)⁻¹ := by
  have h : 0 < 1 + r ^ 2 := by positivity
  rw [shapeRadialMajorant, pow_mul, div_le_iff₀ (pow_pos h _)]
  calc
    (r ^ 2) ^ m ≤ (1 + r ^ 2) ^ m :=
      pow_le_pow_left₀ (sq_nonneg r) (by linarith) _
    _ = (1 + r ^ 2)⁻¹ * (1 + r ^ 2) ^ (m + 1) := by
      rw [pow_succ (1 + r ^ 2) m]
      field_simp

theorem shapeRadialMajorant_integrable (m : ℕ) :
    Integrable (shapeRadialMajorant m) := by
  refine integrable_inv_one_add_sq.mono' ?_ (Filter.Eventually.of_forall fun r => ?_)
  · apply Continuous.aestronglyMeasurable
    unfold shapeRadialMajorant
    have hn : ∀ r : ℝ, (1 + r ^ 2) ^ (m + 1) ≠ 0 := fun r => ne_of_gt (by positivity)
    fun_prop
  · rw [Real.norm_eq_abs, abs_of_nonneg (shapeRadialMajorant_nonneg m r)]
    exact shapeRadialMajorant_le m r

/-- The exact natural-power denominator in the radial shape integral. -/
def shapeQuadratic (Q : ℝ) (c : ℂ) (r : ℝ) : ℂ :=
  (Q : ℂ) + c * (r : ℂ) ^ 2

/-- A fixed positive lower bound valid up to the imaginary boundary along
`c = δ - i d`, with no constant depending on δ. -/
theorem shapeQuadratic_boundary_lower {Q d δ : ℝ} (_hQ : 0 < Q) (hd : 0 < d)
    (hδ : 0 ≤ δ) (r : ℝ) :
    min Q d / 2 * (1 + r ^ 2) ≤ ‖shapeQuadratic Q ((δ : ℂ) - Complex.I * d) r‖ := by
  have hs : (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by norm_cast
  have hre := Complex.re_le_norm (shapeQuadratic Q ((δ : ℂ) - Complex.I * d) r)
  have him := Complex.abs_im_le_norm (shapeQuadratic Q ((δ : ℂ) - Complex.I * d) r)
  have him0 : (shapeQuadratic Q ((δ : ℂ) - Complex.I * d) r).im = -(d * r ^ 2) := by
    simp only [shapeQuadratic, hs, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.sub_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_zero, one_mul, zero_add, zero_sub, neg_mul]
  have him' : d * r ^ 2 ≤ ‖shapeQuadratic Q ((δ : ℂ) - Complex.I * d) r‖ := by
    rw [him0, abs_neg, abs_of_nonneg (mul_nonneg hd.le (sq_nonneg r))] at him
    exact him
  have hre' : Q ≤ ‖shapeQuadratic Q ((δ : ℂ) - Complex.I * d) r‖ := by
    have hre0 : Q + δ * r ^ 2 ≤ ‖shapeQuadratic Q ((δ : ℂ) - Complex.I * d) r‖ := by
      simpa only [shapeQuadratic, hs, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.sub_re, Complex.I_re, Complex.ofReal_im,
        mul_zero, sub_zero, zero_mul, zero_add] using hre
    nlinarith [mul_nonneg hδ (sq_nonneg r)]
  have hminQ := min_le_left Q d
  have hmind := mul_le_mul_of_nonneg_right (min_le_right Q d) (sq_nonneg r)
  nlinarith

/-- Positivity of the same lower constant gives actual denominator nonvanishing. -/
theorem shapeQuadratic_boundary_ne_zero {Q d δ : ℝ} (hQ : 0 < Q) (hd : 0 < d)
    (hδ : 0 ≤ δ) (r : ℝ) :
    shapeQuadratic Q ((δ : ℂ) - Complex.I * d) r ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (by positivity) (shapeQuadratic_boundary_lower hQ hd hδ r)

/-- The literal radial quotient; natural powers preserve its meromorphic meaning. -/
def shapeRadialKernel (m : ℕ) (Q : ℝ) (c : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ (2 * m) / shapeQuadratic Q c r ^ (m + 1)

theorem norm_shapeRadialKernel_le {m : ℕ} {Q r a : ℝ} {c : ℂ} (ha : 0 < a)
    (h : a * (1 + r ^ 2) ≤ ‖shapeQuadratic Q c r‖) :
    ‖shapeRadialKernel m Q c r‖ ≤ (a ^ (m + 1))⁻¹ * shapeRadialMajorant m r := by
  have hn : ‖(r : ℂ) ^ (2 * m)‖ = r ^ (2 * m) := by
    simp [norm_pow, pow_mul]
  rw [shapeRadialKernel, norm_div, hn, norm_pow]
  calc
    r ^ (2 * m) / ‖shapeQuadratic Q c r‖ ^ (m + 1)
        ≤ r ^ (2 * m) / (a * (1 + r ^ 2)) ^ (m + 1) := by
      apply div_le_div_of_nonneg_left (by rw [pow_mul]; positivity)
        (pow_pos (mul_pos ha (by positivity)) _)
      exact pow_le_pow_left₀ (by positivity) h _
    _ = (a ^ (m + 1))⁻¹ * shapeRadialMajorant m r := by
      simp only [shapeRadialMajorant, mul_pow, div_eq_mul_inv, mul_inv_rev]
      ring

theorem shapeRadialKernel_boundary_integrable (m : ℕ) {Q d δ : ℝ}
    (hQ : 0 < Q) (hd : 0 < d) (hδ : 0 ≤ δ) :
    Integrable (shapeRadialKernel m Q ((δ : ℂ) - Complex.I * d)) := by
  refine ((shapeRadialMajorant_integrable m).const_mul
    ((min Q d / 2) ^ (m + 1))⁻¹).mono' ?_ (Filter.Eventually.of_forall fun r => ?_)
  · apply Continuous.aestronglyMeasurable
    have hn : ∀ r : ℝ, shapeQuadratic Q ((δ : ℂ) - Complex.I * d) r ^ (m + 1) ≠ 0 :=
      fun r => pow_ne_zero _ (shapeQuadratic_boundary_ne_zero hQ hd hδ r)
    have hcont : Continuous (shapeQuadratic Q ((δ : ℂ) - Complex.I * d)) := by
      unfold shapeQuadratic
      fun_prop
    unfold shapeRadialKernel
    fun_prop
  · exact norm_shapeRadialKernel_le (by positivity) (shapeQuadratic_boundary_lower hQ hd hδ r)

/-- Nonvanishing of the precise beta factor in the source formula. -/
theorem shapeBeta_ne_zero (k : ℕ) :
    Complex.betaIntegral ((k : ℂ) + 1 / 2) (1 / 2) ≠ 0 := by
  have hk : 0 < (((k : ℂ) + 1 / 2).re) := by simp; positivity
  have hh : 0 < ((1 / 2 : ℂ).re) := by norm_num
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ hk hh]
  apply div_ne_zero
  · exact mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hk)
      (Complex.Gamma_ne_zero_of_re_pos hh)
  · apply Complex.Gamma_ne_zero_of_re_pos
    simpa only [Complex.add_re] using add_pos hk hh

end
end IsingBulk.First
