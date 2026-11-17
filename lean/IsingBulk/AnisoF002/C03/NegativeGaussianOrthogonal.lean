import IsingBulk.AnisoF002.C03.NegativeGaussianFunctional
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Monic Gaussian polynomials and their exact norms

These are the monic physicists' Hermite polynomials, constructed by the
raising operator `X - (1/2) derivative`.  Their entire-line orthogonality
and squared norms are proved from the actual Gaussian integral.  This is
the normalization input for the squared Vandermonde integral, not a
physical or asymptotic premise.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators

noncomputable def monicGaussianPoly : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => X * monicGaussianPoly n - (1 / 2 : ℝ) • (monicGaussianPoly n).derivative

theorem monicGaussianPoly_isMonicOfDegree (n : ℕ) :
    IsMonicOfDegree (monicGaussianPoly n) n := by
  induction n with
  | zero => simp [monicGaussianPoly]
  | succ n ih =>
    have hX : IsMonicOfDegree (X * monicGaussianPoly n) (n + 1) := by
      simpa only [add_comm] using (isMonicOfDegree_X ℝ).mul ih
    exact hX.sub (calc
      ((1 / 2 : ℝ) • (monicGaussianPoly n).derivative).natDegree ≤
          (monicGaussianPoly n).derivative.natDegree := natDegree_smul_le _ _
      _ ≤ (monicGaussianPoly n).natDegree :=
        (natDegree_derivative_le _).trans (Nat.sub_le _ _)
      _ = n := ih.natDegree_eq
      _ < n + 1 := Nat.lt_succ_self n)

theorem gaussianFunctional_monic_mul (n : ℕ) (p : ℝ[X]) :
    gaussianFunctional (monicGaussianPoly n * p) =
      (1 / 2 : ℝ) ^ n * gaussianFunctional (Polynomial.derivative^[n] p) := by
  induction n generalizing p with
  | zero => simp [monicGaussianPoly]
  | succ n ih =>
    rw [monicGaussianPoly, gaussianFunctional_raising, ih, Function.iterate_succ_apply,
      pow_succ]
    ring

theorem monic_iterated_derivative {p : ℝ[X]} {n : ℕ} (hp : IsMonicOfDegree p n) :
    Polynomial.derivative^[n] p = C (n.factorial : ℝ) := by
  ext k
  rw [coeff_iterate_derivative, coeff_C]
  by_cases hk : k = 0
  · subst k
    have hc : p.coeff n = 1 := by
      rw [← hp.natDegree_eq]
      exact hp.monic.coeff_natDegree
    simp [hc, Nat.descFactorial_self]
  · have hc : p.coeff (k + n) = 0 := coeff_eq_zero_of_natDegree_lt (by
      rw [hp.natDegree_eq]
      omega)
    simp [hc, hk]

theorem gaussianFunctional_C (c : ℝ) :
    gaussianFunctional (C c) = c * Real.sqrt Real.pi := by
  change (∫ x : ℝ, (C c).eval x * Real.exp (-x ^ 2)) = _
  simp only [Polynomial.eval_C, integral_const_mul]
  congr 1
  simpa only [neg_mul, one_mul, div_one] using integral_gaussian 1

theorem gaussianFunctional_monic_sq (n : ℕ) :
    gaussianFunctional (monicGaussianPoly n * monicGaussianPoly n) =
      (1 / 2 : ℝ) ^ n * (n.factorial : ℝ) * Real.sqrt Real.pi := by
  rw [gaussianFunctional_monic_mul,
    monic_iterated_derivative (monicGaussianPoly_isMonicOfDegree n), gaussianFunctional_C]
  ring

theorem gaussianFunctional_monic_orthogonal {n m : ℕ} (hnm : n ≠ m) :
    gaussianFunctional (monicGaussianPoly n * monicGaussianPoly m) = 0 := by
  wlog hmn : m < n generalizing n m
  · rw [mul_comm]
    exact this (Ne.symm hnm) (by omega)
  rw [gaussianFunctional_monic_mul, iterate_derivative_eq_zero]
  · simp
  · rw [(monicGaussianPoly_isMonicOfDegree m).natDegree_eq]
    exact hmn

/-- The literal orthogonality and norm formulas needed by the determinant expansion. -/
theorem monicGaussianPoly_integral_product (n m : ℕ) :
    (∫ x : ℝ, (monicGaussianPoly n).eval x * (monicGaussianPoly m).eval x *
      Real.exp (-x ^ 2)) =
      if n = m then (1 / 2 : ℝ) ^ n * (n.factorial : ℝ) * Real.sqrt Real.pi else 0 := by
  have hfun : gaussianFunctional (monicGaussianPoly n * monicGaussianPoly m) =
      if n = m then (1 / 2 : ℝ) ^ n * (n.factorial : ℝ) * Real.sqrt Real.pi else 0 := by
    by_cases h : n = m
    · subst m
      simp only [ite_true, gaussianFunctional_monic_sq]
    · simp only [h, ite_false, gaussianFunctional_monic_orthogonal h]
  simpa only [gaussianFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    Polynomial.eval_mul] using hfun

end
end IsingBulk.AnisoF002.NegativeHT.Angular
