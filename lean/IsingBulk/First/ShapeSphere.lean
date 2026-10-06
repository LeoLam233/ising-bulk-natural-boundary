import IsingBulk.First.ShapeVandermonde
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The positive angular coefficient with its Euclidean polar normalization. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Metric

/-- Euclidean angular measure, normalized by the established polar decomposition. -/
def shapeSphereMeasure (n : ℕ) : Measure (sphere (0 : ShapeSpace n) 1) :=
  (volume : Measure (ShapeSpace n)).toSphere

def shapeSphereIntegral (n : ℕ) : ℝ :=
  ∫ ω : sphere (0 : ShapeSpace n) 1, shapeVandermondeSq ω.1 ∂shapeSphereMeasure n

/-- This is precisely the source angular coefficient including 1/√N. -/
def shapeAngularConstant (n : ℕ) : ℝ :=
  (Real.sqrt (n+1))⁻¹ * shapeSphereIntegral n

theorem shapeSphere_integrable (n : ℕ) :
    Integrable (fun ω : sphere (0 : ShapeSpace n) 1 => shapeVandermondeSq ω.1)
      (shapeSphereMeasure n) := by
  have hc : Continuous (fun ω : sphere (0 : ShapeSpace n) 1 => shapeVandermondeSq ω.1) :=
    (shapeVandermondeSq_continuous n).comp continuous_subtype_val
  change Integrable _ ((volume : Measure (ShapeSpace n)).toSphere)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem shapeSphereIntegral_pos {n : ℕ} (hn : 1 ≤ n) : 0 < shapeSphereIntegral n := by
  unfold shapeSphereIntegral shapeSphereMeasure
  exact integral_pos_of_integrable_nonneg_nonzero
    ((shapeVandermondeSq_continuous n).comp continuous_subtype_val)
    (shapeSphere_integrable n) (fun ω => shapeVandermondeSq_nonneg ω.1)
    (shapeVandermondeSq_distinctShapeUnit_ne_zero hn)

theorem shapeAngularConstant_pos {n : ℕ} (hn : 1 ≤ n) : 0 < shapeAngularConstant n := by
  unfold shapeAngularConstant
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))) (shapeSphereIntegral_pos hn)

end
end IsingBulk.First
