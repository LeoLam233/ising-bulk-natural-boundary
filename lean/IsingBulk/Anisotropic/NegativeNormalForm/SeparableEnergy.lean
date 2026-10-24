import IsingBulk.Anisotropic.NegativeNormalForm.Algebra
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Exact separable energy algebra, ANISO (4.12)–(4.18).
This file does not claim the uniform implicit-function theorem or the removable
analytic regularity of the quotient. It proves the exact identity from the actual
pole equation, including all zero-coordinate cases. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

/-- The Taylor remainder with the linear term removed. -/
def energyRemainder (g : ℂ → ℂ) (gd d v : ℂ) : ℂ :=
  g (d + v) - g d - gd * v

/-- The quotient in (4.13), with its derivative-defined removable value at zero.
Its holomorphic removable extension is a separate analytic obligation. -/
def energyQuotient (g : ℂ → ℂ) (gd d h a v : ℂ) : ℂ :=
  if v = 0 then -(deriv (deriv g) d) / (h * a) else -(2 * energyRemainder g gd d v) / (h * a * v ^ 2)

theorem energyRemainder_zero (g : ℂ → ℂ) (gd d : ℂ) :
    energyRemainder g gd d 0 = 0 := by simp [energyRemainder]

theorem energyQuotient_mul (g : ℂ → ℂ) (gd d h a v : ℂ)
    (hh : h ≠ 0) (ha : a ≠ 0) :
    h * a * (v ^ 2 * energyQuotient g gd d h a v) =
      -(2 * energyRemainder g gd d v) := by
  by_cases hv : v = 0
  · subst v
    simp [energyRemainder, energyQuotient]
  · simp only [energyQuotient, hv, ↓reduceIte]
    field_simp

/-- Sum of the true one-body Taylor remainders at a pole, using the exact
zero-mean constraint and not a surrogate quadratic pole equation. -/
theorem sum_energyRemainder_at_pole {n : ℕ} (g : ℂ → ℂ)
    (gd d gamma : ℂ) (v : Config n) (hv : ZeroMean v)
    (hpole : ∑ i, (g (d + v i) - gamma) = 0) :
    (∑ i, energyRemainder g gd d (v i)) = -(n : ℂ) * (g d - gamma) := by
  simp only [energyRemainder, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ZeroMean] at *
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at *
  rw [hv]
  linear_combination hpole

/-- Equation (4.17), with the divided difference `a` specified by its
actual one-body value. All coordinate coincidences are included. -/
theorem separable_energy_identity {n : ℕ} (hn : n ≠ 0) (g : ℂ → ℂ)
    (gd d gamma h a t tau : ℂ) (v : Config n) (hv : ZeroMean v)
    (hh : h ≠ 0) (ha : a ≠ 0)
    (ha_value : g d - gamma = a * (t - tau))
    (hpole : ∑ i, (g (d + v i) - gamma) = 0) :
    t - tau = h / (2 * n) * ∑ i, (v i)^2 * energyQuotient g gd d h a (v i) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hs := sum_energyRemainder_at_pole g gd d gamma v hv hpole
  rw [ha_value] at hs
  have hmul : h * a * (∑ i, (v i)^2 * energyQuotient g gd d h a (v i)) =
      -2 * ∑ i, energyRemainder g gd d (v i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [neg_mul] using energyQuotient_mul g gd d h a (v i) hh ha
  rw [hs] at hmul
  field_simp
  apply mul_right_cancel₀ ha
  linear_combination -hmul

/-- The componentwise square-root map in (4.18), before projection. -/
def separableMap {n : ℕ} (g : ℂ → ℂ) (gd d h a : ℂ) (v : Config n) : Config n :=
  fun i => v i * Complex.sqrt (energyQuotient g gd d h a (v i))

theorem quadratic_separableMap {n : ℕ} (g : ℂ → ℂ) (gd d h a : ℂ) (v : Config n) :
    quadratic (separableMap g gd d h a v) =
      ∑ i, (v i)^2 * energyQuotient g gd d h a (v i) := by
  simp [quadratic, separableMap, mul_pow, sqrt_sq]

end
end IsingBulk.Anisotropic.NegativeNormalForm
