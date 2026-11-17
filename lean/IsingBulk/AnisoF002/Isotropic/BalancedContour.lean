import Mathlib.Basic.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# F002: balanced contour algebra

New proofs of the finite-dimensional identities in F002
`eq:iso-balanced-deformation`.  This file imports no historical Ising proof.
The later analytic assertion that the holomorphic integral is invariant
under this deformation is a separate obligation.
-/

namespace IsingBulk.AnisoF002.Isotropic

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The exact real balanced displacement, with `scale = τ / N`. -/
def balancedShift (scale : ℝ) (p m : ι → ℝ) (i : ι) : ℝ :=
  scale * ((∑ j, p j) * m i - (∑ j, m j) * p i)

/-- The displacement stays in the original zero-total-angle tangent plane. -/
theorem sum_balancedShift (scale : ℝ) (p m : ι → ℝ) :
    ∑ i, balancedShift scale p m i = 0 := by
  simp only [balancedShift]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- At complete equality the deformation vanishes coordinatewise. -/
theorem balancedShift_of_constant (scale p₀ m₀ : ℝ) (i : ι) :
    balancedShift scale (fun _ : ι => p₀) (fun _ => m₀) i = 0 := by
  simp only [balancedShift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- Reflection exchanges the two bump populations and reverses the shift. -/
theorem balancedShift_swap (scale : ℝ) (p m : ι → ℝ) (i : ι) :
    balancedShift scale m p i = -balancedShift scale p m i := by
  unfold balancedShift
  ring

/-- Exact pair difference with the actual global populations retained. -/
theorem balancedShift_sub (scale : ℝ) (p m : ι → ℝ) (i j : ι) :
    balancedShift scale p m i - balancedShift scale p m j =
      scale * ((∑ l, p l) * (m i - m j) -
        (∑ l, m l) * (p i - p j)) := by
  unfold balancedShift
  ring

/-- For disjoint bumps, upper support moves inward. -/
theorem balancedShift_nonpos_of_lower_zero
    (scale : ℝ) (p m : ι → ℝ) (i : ι)
    (hs : 0 ≤ scale) (hp : 0 ≤ p i) (hm : ∀ j, 0 ≤ m j)
    (hmi : m i = 0) : balancedShift scale p m i ≤ 0 := by
  unfold balancedShift
  rw [hmi, mul_zero, zero_sub]
  exact mul_nonpos_of_nonneg_of_nonpos hs
    (neg_nonpos.mpr (mul_nonneg (Finset.sum_nonneg fun j _ => hm j) hp))

/-- For disjoint bumps, lower support moves outward. -/
theorem balancedShift_nonneg_of_upper_zero
    (scale : ℝ) (p m : ι → ℝ) (i : ι)
    (hs : 0 ≤ scale) (hm : 0 ≤ m i) (hp : ∀ j, 0 ≤ p j)
    (hpi : p i = 0) : 0 ≤ balancedShift scale p m i := by
  unfold balancedShift
  rw [hpi, mul_zero, sub_zero]
  exact mul_nonneg hs (mul_nonneg (Finset.sum_nonneg fun j _ => hp j) hm)

/-- Coordinates at the final contour, before introducing regular inverses. -/
def contourCoordinate (θ h : ι → ℝ) (i : ι) : ℂ :=
  (θ i : ℂ) - Complex.I * (h i : ℂ)

/-- The actual complex contour has exactly the original sum of angles. -/
theorem sum_contourCoordinate (θ : ι → ℝ) (scale : ℝ) (p m : ι → ℝ) :
    ∑ i, contourCoordinate θ (balancedShift scale p m) i =
      ((∑ i, θ i : ℝ) : ℂ) := by
  simp only [contourCoordinate, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Complex.ofReal_sum, sum_balancedShift, Complex.ofReal_zero, mul_zero, sub_zero]

/-- The smooth partition used only after the whole-torus deformation sums to one. -/
theorem exact_partition (ηP ηQ : ℝ) :
    ηP * ηQ + (1 / 2 : ℝ) * (1 - ηP) * (1 + ηQ) +
      (1 / 2 : ℝ) * (1 - ηQ) * (1 + ηP) = 1 := by
  ring

end IsingBulk.AnisoF002.Isotropic
