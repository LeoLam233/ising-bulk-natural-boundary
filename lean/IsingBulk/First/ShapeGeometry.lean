import IsingBulk.First.MeanCoordinates
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! The genuine Euclidean zero-sum hyperplane for the FIRST period. The
coordinate parameter is n, and the number of particles is n+1. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Module
open scoped BigOperators InnerProductSpace

/-- Coordinate sum on the ambient Euclidean particle space. -/
def shapeSum (n : ℕ) : EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]

/-- Intrinsic Euclidean hyperplane, not a restriction of ambient Lebesgue measure. -/
def shapeSubspace (n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin (n+1))) :=
  (shapeSum n).ker

abbrev ShapeSpace (n : ℕ) := shapeSubspace n

@[simp] theorem mem_shapeSubspace {n : ℕ} (x : EuclideanSpace ℝ (Fin (n+1))) :
    x ∈ shapeSubspace n ↔ ∑ i, x i = 0 := Iff.rfl

/-- The last coordinate is exactly minus the sum of the first n coordinates. -/
def shapeCoordinateEquiv (n : ℕ) : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] ShapeSpace n where
  toFun t := ⟨WithLp.toLp 2 (shapeExtend (fun i => t i)), by
    exact sum_shapeExtend (fun i => t i)⟩
  invFun x := WithLp.toLp 2 (fun i => x.1 i.castSucc)
  left_inv t := by
    ext i
    simp
  right_inv x := by
    apply Subtype.ext
    have h := shapeExtend_restrict (fun i => x.1 i) x.2
    exact congrArg (WithLp.toLp 2) h
  map_add' t u := by
    apply Subtype.ext
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Finset.sum_add_distrib, add_comm]
    · simp
  map_smul' a t := by
    apply Subtype.ext
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Finset.mul_sum]
    · simp

@[simp] theorem shapeCoordinateEquiv_apply {n : ℕ}
    (t : EuclideanSpace ℝ (Fin n)) (i : Fin (n+1)) :
    (shapeCoordinateEquiv n t).1 i = shapeExtend (fun j => t j) i := rfl

@[simp] theorem finrank_shapeSpace (n : ℕ) : finrank ℝ (ShapeSpace n) = n := by
  rw [← (shapeCoordinateEquiv n).finrank_eq]
  exact finrank_euclideanSpace_fin

/-- The dependent last coordinate changes the quadratic form. -/
theorem norm_sq_shapeCoordinateEquiv {n : ℕ} (t : EuclideanSpace ℝ (Fin n)) :
    ‖shapeCoordinateEquiv n t‖ ^ 2 = (∑ i, (t i) ^ 2) + (∑ i, t i) ^ 2 := by
  change ‖(shapeCoordinateEquiv n t).1‖ ^ 2 = _
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp

theorem inner_shapeCoordinateEquiv {n : ℕ} (t u : EuclideanSpace ℝ (Fin n)) :
    ⟪shapeCoordinateEquiv n t, shapeCoordinateEquiv n u⟫_ℝ =
      ⟪t, u⟫_ℝ + (∑ i, t i) * (∑ i, u i) := by
  change ⟪(shapeCoordinateEquiv n t).1, (shapeCoordinateEquiv n u).1⟫_ℝ = _
  rw [PiLp.inner_apply, Fin.sum_univ_castSucc, PiLp.inner_apply]
  simp [mul_comm]

/-- Gram matrix of the actual last-coordinate embedding. -/
theorem gram_shapeCoordinateEquiv (n : ℕ) :
    Matrix.gram ℝ (fun i => shapeCoordinateEquiv n (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      (1 : Matrix (Fin n) (Fin n) ℝ) +
        Matrix.replicateCol Unit (fun _ : Fin n => (1 : ℝ)) *
        Matrix.replicateRow Unit (fun _ : Fin n => (1 : ℝ)) := by
  ext i j
  change ⟪shapeCoordinateEquiv n (EuclideanSpace.basisFun (Fin n) ℝ i),
    shapeCoordinateEquiv n (EuclideanSpace.basisFun (Fin n) ℝ j)⟫_ℝ = _
  rw [inner_shapeCoordinateEquiv]
  simp [EuclideanSpace.basisFun_apply, Matrix.mul_apply, PiLp.single_apply, Matrix.one_apply,
    PiLp.inner_apply, eq_comm]

/-- The squared Euclidean volume Jacobian is the particle number. -/
theorem shapeCoordinateEquiv_normDet_sq (n : ℕ) :
    (shapeCoordinateEquiv n).toLinearMap.normDet ^ 2 = (n+1 : ℝ) := by
  have h := (shapeCoordinateEquiv n).toLinearMap.normDet_sq_eq_det_gram
    (EuclideanSpace.basisFun (Fin n) ℝ)
  change (shapeCoordinateEquiv n).toLinearMap.normDet ^ 2 =
    (Matrix.gram ℝ (fun i => shapeCoordinateEquiv n (EuclideanSpace.basisFun (Fin n) ℝ i))).det at h
  rw [gram_shapeCoordinateEquiv, Matrix.det_one_add_replicateCol_mul_replicateRow] at h
  simpa [dotProduct, add_comm] using h

theorem shapeCoordinateEquiv_normDet (n : ℕ) :
    (shapeCoordinateEquiv n).toLinearMap.normDet = Real.sqrt (n+1) := by
  have h := shapeCoordinateEquiv_normDet_sq n
  have hp := (shapeCoordinateEquiv n).toLinearMap.normDet_nonneg
  nlinarith [Real.sq_sqrt (show 0 ≤ (n+1 : ℝ) by positivity),
    Real.sqrt_nonneg (n+1 : ℝ)]

end
end IsingBulk.First
