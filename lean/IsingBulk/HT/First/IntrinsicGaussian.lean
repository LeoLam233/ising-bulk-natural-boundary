import IsingBulk.HT.First.ShapeMeanGaussian
import IsingBulk.HT.First.GaussianVandermonde

/-! Gaussian normalization on the literal intrinsic ShapeSpace, with the
actual ambient integrability and determinant integral supplied by the
proved Hermite/finite-Fubini chain. No analytic premise is exposed here. -/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.First MeasureTheory
open scoped BigOperators

theorem gaussian_vandermonde_mean_split (n : ℕ) :
    (∫ y : Fin (n+1) → ℝ,Real.exp (-(∑ i,y i^2)/2)*(firstVandermonde y)^2)=
      Real.sqrt (2*Real.pi)*∫ x : ShapeSpace n,
        shapeVandermondeSq x*Real.exp (-‖x‖^2/2) :=
  gaussian_vandermonde_mean_split_of_integrable n
    (Gaussian.ambient_gaussian_firstVandermonde_integrable (n+1))

/-- Actual intrinsic Gaussian-polynomial integrability, obtained by the
measure-preserving unit-mean split and the integrable marginal theorem. -/
theorem intrinsic_gaussian_shape_integrable (n : ℕ) :
    Integrable (fun x : ShapeSpace n =>
      shapeVandermondeSq x*Real.exp (-‖x‖^2/2)) := by
  have hi := (unitMeanShape_measurePreserving n).integrable_comp_of_integrable
    (Gaussian.ambient_gaussian_firstVandermonde_integrable (n+1))
  have hi' : Integrable (fun z : ℝ × ShapeSpace n =>
      Real.exp (-(∑ i,unitMeanShapeChart z.1 z.2 i^2)/2)*
        (firstVandermonde (unitMeanShapeChart z.1 z.2))^2)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hi
  have hm := hi'.integral_prod_right
  simp_rw [unitMeanShape_gaussian_factor,integral_const_mul,
    integral_unit_mean_gaussian] at hm
  have hc : Real.sqrt (2*Real.pi) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  exact (integrable_mul_const_iff (isUnit_iff_ne_zero.2 hc) _).mp hm

/-- Intrinsic volume, with unit mean removed. The separate free-coordinate
factor 1/√(n+1) has not yet been applied. -/
theorem intrinsic_gaussian_shape_integral (n : ℕ) :
    (∫ x : ShapeSpace n,shapeVandermondeSq x*Real.exp (-‖x‖^2/2))=
      (Real.sqrt (2*Real.pi))^n*∏ m ∈ Finset.Icc 1 (n+1),(m.factorial:ℝ) := by
  have h := Gaussian.ambient_gaussian_vandermonde_integral (n+1)
  change (∫ y : Fin (n+1) → ℝ,Real.exp (-(∑ i,y i^2)/2)*(firstVandermonde y)^2)=
    (Real.sqrt (2*Real.pi))^(n+1)*∏ m ∈ Finset.Icc 1 (n+1),(m.factorial:ℝ) at h
  rw [gaussian_vandermonde_mean_split,pow_succ] at h
  have hc : Real.sqrt (2*Real.pi) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  apply mul_left_cancel₀ hc
  calc
    _ = (Real.sqrt (2*Real.pi))^n*Real.sqrt (2*Real.pi)*
        ∏ m ∈ Finset.Icc 1 (n+1),(m.factorial:ℝ) := h
    _ = _ := by ring

end
end IsingBulk.HT.First
