import IsingBulk.First.ShapeScaledDenominator
import IsingBulk.First.ShapeDominatedLimit

/-! Intrinsic Euclidean versions of the actual denominator's nonlinear gap and
fixed-shape limit. Both inputs to dominated convergence are proved for the
literal radius-free physical expression. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Set Filter
open scoped Topology BigOperators

def intrinsicShapeCoordinates {n : ℕ} (x : ShapeSpace n) : Fin n → ℝ :=
  fun j => x.1 j.castSucc

@[simp] theorem shapeExtend_intrinsicShapeCoordinates {n : ℕ} (x : ShapeSpace n) :
    shapeExtend (intrinsicShapeCoordinates x) = fun j => x.1 j :=
  shapeExtend_restrict (fun j => x.1 j) x.2

@[simp] theorem intrinsicShapeCoordinates_smul {n : ℕ} (lam : ℝ) (x : ShapeSpace n) :
    intrinsicShapeCoordinates (lam • x) = lam • intrinsicShapeCoordinates x := rfl

theorem intrinsicShapeCoordinates_continuous (n : ℕ) :
    Continuous (@intrinsicShapeCoordinates n) := by
  apply continuous_pi
  intro j
  exact (EuclideanSpace.proj j.castSucc).continuous.comp continuous_subtype_val

theorem intrinsic_shape_square_sum {n : ℕ} (x : ShapeSpace n) :
    (∑ j, (shapeExtend (intrinsicShapeCoordinates x) j)^2) = ‖x‖^2 := by
  rw [shapeExtend_intrinsicShapeCoordinates]
  exact (EuclideanSpace.real_norm_sq_eq x.1).symm

def actualShapeDenominator {n : ℕ} (a : OrderedChartData) (epsilon : ℝ)
    (x : ShapeSpace n) : ℂ :=
  shapePoleDenominator (radialParameter a.theta epsilon) a.alpha (intrinsicShapeCoordinates x)

/-- One positive constant and one neighborhood control all source parameters
and shapes in the support ball. -/
theorem actualShapeDenominator_uniform_lower {n : ℕ} (a : OrderedChartData)
    (hb : Complex.exp (-(n+1:ℂ)*(a.beta:ℂ)*Complex.I) = 1) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ epsilon : ℝ, ∀ x : ShapeSpace n,
      0 < epsilon → epsilon < r → ‖x‖ < r →
      c*(epsilon+‖x‖^2) ≤ ‖actualShapeDenominator a epsilon x‖ := by
  obtain ⟨c,r,hc,hr,h⟩ := actual_shape_denominator_lower_bound_ball a n hb
  refine ⟨c,r,hc,hr,?_⟩
  intro epsilon x he her hxr
  have hs : (∑ j, (shapeExtend (intrinsicShapeCoordinates x) j)^2) < r^2 := by
    rw [intrinsic_shape_square_sum]
    nlinarith [norm_nonneg x]
  simpa only [actualShapeDenominator, intrinsic_shape_square_sum] using h epsilon (intrinsicShapeCoordinates x) he her hs

/-- The exact intrinsic pointwise limit required by the already proved
post-mean dominated convergence theorem. -/
theorem actualShapeDenominator_scale_limit {n : ℕ} (a : OrderedChartData)
    (hb : Complex.exp (-(n+1:ℂ)*(a.beta:ℂ)*Complex.I) = 1) (x : ShapeSpace n) :
    Tendsto (fun lam : ℝ => actualShapeDenominator a (lam^2) (lam • x)/(lam:ℂ)^2)
      (𝓝[>] 0) (𝓝 ((a.Q (n+1):ℂ)-Complex.I*(a.d:ℂ)*(‖x‖:ℂ)^2)) := by
  have h := actual_shape_denominator_scale_limit a (intrinsicShapeCoordinates x) hb
  have hs : (∑ j, ((shapeExtend (intrinsicShapeCoordinates x) j:ℝ):ℂ)^2) = (‖x‖:ℂ)^2 := by
    exact_mod_cast intrinsic_shape_square_sum x
  simpa only [actualShapeDenominator, intrinsicShapeCoordinates_smul, hs] using h

theorem actualShapeDenominator_sqrt_limit {n : ℕ} (a : OrderedChartData)
    (hb : Complex.exp (-(n+1:ℂ)*(a.beta:ℂ)*Complex.I) = 1) (x : ShapeSpace n) :
    Tendsto (fun epsilon : ℝ => actualShapeDenominator a epsilon (Real.sqrt epsilon • x)/(epsilon:ℂ))
      (𝓝[>] 0) (𝓝 ((a.Q (n+1):ℂ)-Complex.I*(a.d:ℂ)*(‖x‖:ℂ)^2)) := by
  have h := actual_shape_denominator_sqrt_limit a (intrinsicShapeCoordinates x) hb
  have hs : (∑ j, ((shapeExtend (intrinsicShapeCoordinates x) j:ℝ):ℂ)^2) = (‖x‖:ℂ)^2 := by
    exact_mod_cast intrinsic_shape_square_sum x
  simpa only [actualShapeDenominator, intrinsicShapeCoordinates_smul, hs] using h

end
end IsingBulk.First
