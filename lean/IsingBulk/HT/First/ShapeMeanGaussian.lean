import IsingBulk.HT.First.ShapeMeanGeometry
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Exact √(2π) mean factor for the actual intrinsic ShapeSpace Gaussian.
The integrability input below is discharged by the actual determinant
Gaussian integrability theorem in the final numerical evaluation adapter. -/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.First MeasureTheory
open scoped BigOperators

theorem integral_unit_mean_gaussian :
    (∫ u : ℝ,Real.exp (-(u^2)/2))=Real.sqrt (2*Real.pi) := by
  have hfun : (fun u : ℝ => Real.exp (-(u^2)/2))=
      (fun u : ℝ => Real.exp (-(1/2:ℝ)*u^2)) := by
    funext u
    congr 1
    ring
  rw [hfun,integral_gaussian]
  congr 1
  ring

theorem unitMeanShape_gaussian_factor {n : ℕ} (x : ShapeSpace n) (u : ℝ) :
    Real.exp (-(∑ i,unitMeanShapeChart u x i^2)/2)*
      (firstVandermonde (unitMeanShapeChart u x))^2=
    (shapeVandermondeSq x*Real.exp (-‖x‖^2/2))*Real.exp (-(u^2)/2) := by
  rw [unitMeanShapeChart_square_sum,firstVandermonde_unitMeanShapeChart,
    show -(u^2+‖x‖^2)/2=-(u^2)/2 + -‖x‖^2/2 by ring,Real.exp_add]
  unfold shapeVandermondeSq
  ring

/-- The ambient product-Lebesgue Gaussian Vandermonde integral has exactly
one √(2π) mean factor. No free-coordinate √(n+1) enters this identity. -/
theorem gaussian_vandermonde_mean_split_of_integrable (n : ℕ)
    (hF : Integrable (fun y : Fin (n+1) → ℝ =>
      Real.exp (-(∑ i,y i^2)/2)*(firstVandermonde y)^2)) :
    (∫ y : Fin (n+1) → ℝ,Real.exp (-(∑ i,y i^2)/2)*(firstVandermonde y)^2)=
      Real.sqrt (2*Real.pi)*∫ x : ShapeSpace n,
        shapeVandermondeSq x*Real.exp (-‖x‖^2/2) := by
  rw [integral_unitMeanShapeChart n _ hF]
  simp_rw [unitMeanShape_gaussian_factor,integral_const_mul,integral_unit_mean_gaussian]
  rw [integral_mul_const]
  ring

end
end IsingBulk.HT.First
