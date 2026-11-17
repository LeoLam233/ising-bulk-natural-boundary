import IsingBulk.AnisoF002.C03.NegativeAngularRadial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The Gaussian polynomial functional needed for the actual Mehta normalization

This proves integrability and the Gaussian integration-by-parts identity
on the entire real line.  It is the analytic step behind the monic
physicists' Hermite polynomial computation in frozen F002, Section 3.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators

theorem polynomial_gaussian_integrable (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x * Real.exp (-x ^ 2)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add, add_mul] using hp.fun_add hq
  | monomial n a =>
    have hn : -1 < (n : ℝ) := by have h := Nat.cast_nonneg (α := ℝ) n; linarith
    have h : Integrable (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) := by
      simpa only [Real.rpow_natCast, neg_mul, one_mul] using
        (integrable_rpow_mul_exp_neg_mul_sq (b := 1) zero_lt_one hn)
    simpa only [Polynomial.eval_monomial, mul_assoc] using h.const_mul a

def gaussianFunctional : ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := ∫ x : ℝ, p.eval x * Real.exp (-x ^ 2)
  map_add' p q := by
    simp only [Polynomial.eval_add, add_mul]
    exact integral_add (polynomial_gaussian_integrable p) (polynomial_gaussian_integrable q)
  map_smul' a p := by
    simp only [Polynomial.eval_smul, smul_eq_mul, mul_assoc, RingHom.id_apply]
    exact integral_const_mul a _

theorem hasDerivAt_gaussian_weight (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2)) (-2 * x * Real.exp (-x ^ 2)) x := by
  convert (((hasDerivAt_id x).pow 2).neg.exp) using 1
  · rfl
  · simp only [Pi.neg_apply, Pi.pow_apply, id_eq, mul_one, Nat.cast_ofNat]
    ring

theorem gaussianFunctional_stein (p : ℝ[X]) :
    gaussianFunctional p.derivative = 2 * gaussianFunctional (X * p) := by
  have hleft : Integrable (fun x : ℝ => p.eval x * (-2 * x * Real.exp (-x ^ 2))) := by
    convert (polynomial_gaussian_integrable (X * p)).const_mul (-2) using 1
    ext x
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
    ring
  have hright : Integrable (fun x : ℝ => p.derivative.eval x * Real.exp (-x ^ 2)) :=
    polynomial_gaussian_integrable p.derivative
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => p.eval x) (v := fun x : ℝ => Real.exp (-x ^ 2))
    (u' := fun x : ℝ => p.derivative.eval x)
    (v' := fun x : ℝ => -2 * x * Real.exp (-x ^ 2))
    (fun x _ => p.hasDerivAt x) (fun x _ => hasDerivAt_gaussian_weight x)
    hleft hright (polynomial_gaussian_integrable p)
  have he : (fun x : ℝ => p.eval x * (-2 * x * Real.exp (-x ^ 2))) =
      fun x : ℝ => -2 * ((X * p).eval x * Real.exp (-x ^ 2)) := by
    funext x
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
    ring
  rw [he, integral_const_mul] at h
  change -2 * gaussianFunctional (X * p) = -gaussianFunctional p.derivative at h
  linarith

/-- The exact raising/lowering identity for the monic Gaussian polynomials. -/
theorem gaussianFunctional_raising (p q : ℝ[X]) :
    gaussianFunctional ((X * p - (1 / 2 : ℝ) • p.derivative) * q) =
      (1 / 2 : ℝ) * gaussianFunctional (p * q.derivative) := by
  have h := gaussianFunctional_stein (p * q)
  rw [Polynomial.derivative_mul, map_add] at h
  have he : (X * p - (1 / 2 : ℝ) • p.derivative) * q =
      X * (p * q) - (1 / 2 : ℝ) • (p.derivative * q) := by
    simp only [smul_eq_C_mul]
    ring
  rw [he, map_sub, map_smul]
  change gaussianFunctional (X * (p * q)) -
    (1 / 2 : ℝ) * gaussianFunctional (p.derivative * q) = _
  linarith

end
end IsingBulk.AnisoF002.NegativeHT.Angular
