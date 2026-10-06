import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! The actual mean/zero-sum coordinates for the first singular chart.
The last shape coordinate is minus the sum of the preceding coordinates.
No integral identity or estimate is a premise of this coordinate layer. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

/-- The manuscript convention for its dependent final shape coordinate. -/
def shapeExtend {K : Type*} [AddCommGroup K] {n : ℕ} (t : Fin n → K) :
    Fin (n+1) → K := Fin.snoc t (-∑ j, t j)

@[simp] theorem shapeExtend_castSucc {K : Type*} [AddCommGroup K] {n : ℕ}
    (t : Fin n → K) (j : Fin n) : shapeExtend t j.castSucc = t j := by
  simp [shapeExtend]

@[simp] theorem shapeExtend_last {K : Type*} [AddCommGroup K] {n : ℕ}
    (t : Fin n → K) : shapeExtend t (Fin.last n) = -∑ j, t j := by
  simp [shapeExtend]

@[simp] theorem sum_shapeExtend {K : Type*} [AddCommGroup K] {n : ℕ}
    (t : Fin n → K) : ∑ j, shapeExtend t j = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp

/-- Every zero-sum tuple is recovered from its first n entries. -/
theorem shapeExtend_restrict {K : Type*} [AddCommGroup K] {n : ℕ}
    (u : Fin (n+1) → K) (hu : ∑ j, u j = 0) :
    shapeExtend (fun j => u j.castSucc) = u := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [shapeExtend_last]
    rw [Fin.sum_univ_castSucc] at hu
    exact (eq_neg_of_add_eq_zero_right hu).symm
  · simp

/-- Sum of angular deviations, not their average. -/
def meanCoordinate {K : Type*} [AddCommMonoid K] {N : ℕ} (u : Fin N → K) : K :=
  ∑ j, u j

/-- All N zero-sum deviations in the source chart. -/
def shapeCoordinates {K : Type*} [Field K] {N : ℕ} (u : Fin N → K) : Fin N → K :=
  fun j => u j - meanCoordinate u / N

theorem sum_shapeCoordinates {K : Type*} [Field K] {N : ℕ}
    (hN : (N : K) ≠ 0) (u : Fin N → K) : ∑ j, shapeCoordinates u j = 0 := by
  simp only [shapeCoordinates, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  unfold meanCoordinate
  field_simp
  ring

/-- Inverse of the manuscript coordinates, with the source mean kept first. -/
def meanShapeChart {K : Type*} [Field K] {n : ℕ} (v : K) (t : Fin n → K) :
    Fin (n+1) → K := fun j => shapeExtend t j + v / (n+1)

theorem meanCoordinate_meanShapeChart {K : Type*} [Field K] {n : ℕ}
    (hN : (n+1 : K) ≠ 0) (v : K) (t : Fin n → K) :
    meanCoordinate (meanShapeChart v t) = v := by
  simp only [meanCoordinate, meanShapeChart, Finset.sum_add_distrib, sum_shapeExtend,
    zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

theorem shapeCoordinates_meanShapeChart {K : Type*} [Field K] {n : ℕ}
    (hN : (n+1 : K) ≠ 0) (v : K) (t : Fin n → K) :
    shapeCoordinates (meanShapeChart v t) = shapeExtend t := by
  funext j
  simp only [shapeCoordinates, meanCoordinate_meanShapeChart hN, meanShapeChart]
  push_cast
  ring

theorem meanShapeChart_coordinates {K : Type*} [Field K] {n : ℕ}
    (hN : (n+1 : K) ≠ 0) (u : Fin (n+1) → K) :
    meanShapeChart (meanCoordinate u) (fun j => shapeCoordinates u j.castSucc) = u := by
  have hzero : ∑ j, shapeCoordinates u j = 0 := sum_shapeCoordinates (by simpa using hN) u
  have he := shapeExtend_restrict (shapeCoordinates u) hzero
  funext j
  change shapeExtend (fun j => shapeCoordinates u j.castSucc) j +
    meanCoordinate u / (n+1) = u j
  rw [he]
  simp only [shapeCoordinates]
  push_cast
  ring

end
end IsingBulk.First
