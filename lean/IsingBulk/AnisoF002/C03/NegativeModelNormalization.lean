import IsingBulk.AnisoF002.C03.NegativeQuadraticPeriods
import IsingBulk.AnisoF002.NegativeHT.ComplexModel

/-!
# Exact scalar normalizations for the physical negative-HT model

The independent-coordinate Mehta integral is matched to the frozen finite
factorial product.  The original model is rewritten with ordinary integer
powers, retaining its principal square root explicitly.  This exposes the
single branch factor that must be retained when the actual physical square
root is attached.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open MeasureTheory Angular
open scoped BigOperators

theorem constrainedMehtaProduct_eq_factorialProduct (d : ℕ) :
    constrainedMehtaProduct d = factorialProduct (d + 1) := by
  rw [constrainedMehtaProduct, factorialProduct, Finset.prod_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, mul_one]
  rw [Finset.prod_range]

theorem constrainedGaussianIntegral_odd_exact (k : ℕ) :
    constrainedGaussianIntegral (2 * k) =
      ((2 * k + 1).factorial : ℝ) * Real.pi ^ k * factorialProduct (2 * k + 1) /
        Real.sqrt ((2 * k + 1 : ℕ) : ℝ) := by
  rw [constrained_gaussian_mehta, constrainedMehtaProduct_eq_factorialProduct,
    pow_mul, Real.sq_sqrt Real.pi_pos.le]

theorem positive_rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem model_natural_power_form (k j : ℕ) {B h : ℂ} (hB : B ≠ 0)
    (s τ : ℝ) :
    modelCoefficient (2 * k + 1) j B h s τ =
      -(4 * B ^ (2 * k * (k + 1)) * (factorialProduct (2 * k + 1) : ℂ) *
        ((2 * k + 1 : ℕ) : ℂ) ^ (2 * k * (k + 1)) *
        (τ : ℂ) ^ (2 * k * (k + 1)) *
        (gammaQuotient j (2 * k * (k + 1)) : ℂ)) /
      ((2 : ℂ) ^ (2 * k * (k + 1)) * Complex.sqrt B *
        ((2 * k + 1 : ℕ) : ℂ) * (Real.sqrt ((2 * k + 1 : ℕ) : ℝ) : ℂ) *
        (Real.pi : ℂ) ^ k * (s : ℂ) ^ (2 * (2 * k * (k + 1))) *
        h ^ (2 * k * (k + 1)) * (τ : ℂ) ^ (j + 1)) := by
  let a := 2 * k * (k + 1)
  have hn : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have htwo : (2 : ℝ) ^ (2 - (a : ℝ)) = 4 / (2 : ℝ) ^ a := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]
    norm_num
  have hnp : (((2 * k + 1 : ℕ) : ℝ)) ^ ((a : ℝ) - 3 / 2) =
      (((2 * k + 1 : ℕ) : ℝ)) ^ a /
        (((2 * k + 1 : ℕ) : ℝ) * Real.sqrt ((2 * k + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_sub hn, Real.rpow_natCast, positive_rpow_three_halves hn]
  have hpi : Real.pi ^ ((((2 * k + 1 : ℕ) : ℝ) - 1) / 2) = Real.pi ^ k := by
    have he : ((((2 * k + 1 : ℕ) : ℝ) - 1) / 2) = (k : ℝ) := by push_cast; ring
    rw [he, Real.rpow_natCast]
  have hbpow : B ^ (((a : ℝ) - 1 / 2 : ℝ) : ℂ) = B ^ a / Complex.sqrt B := by
    push_cast
    rw [Complex.cpow_sub _ _ hB, Complex.cpow_natCast]
    simp only [Complex.sqrt, one_div]
  have hhpow : h ^ ((-(a : ℝ) : ℝ) : ℂ) = (h ^ a)⁻¹ := by
    push_cast
    rw [Complex.cpow_neg, Complex.cpow_natCast]
  rw [modelCoefficient, particleExponent_odd]
  change -(((2 : ℝ) ^ (2 - (a : ℝ)) : ℝ) : ℂ) *
    B ^ (((a : ℝ) - 1 / 2 : ℝ) : ℂ) * (factorialProduct (2 * k + 1) : ℂ) *
    (((((2 * k + 1 : ℕ) : ℝ)) ^ ((a : ℝ) - 3 / 2) : ℝ) : ℂ) /
    ((Real.pi ^ ((((2 * k + 1 : ℕ) : ℝ) - 1) / 2) * s ^ (2 * a) : ℝ) : ℂ) *
    h ^ ((-(a : ℝ) : ℝ) : ℂ) *
    ((τ ^ a / τ ^ (j + 1) * gammaQuotient j a : ℝ) : ℂ) = _
  rw [htwo, hnp, hpi, hbpow, hhpow]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end
end IsingBulk.AnisoF002.NegativeHT
