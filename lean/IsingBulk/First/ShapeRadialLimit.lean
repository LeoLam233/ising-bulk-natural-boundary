import IsingBulk.First.ShapeRadialBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual dominated boundary continuation of the constrained radial integral. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

/-- The genuine positive-radius integral, before its beta evaluation. -/
def shapeRadialIntegral (k : ℕ) (Q : ℝ) (c : ℂ) : ℂ :=
  ∫ r : ℝ in Ioi 0, shapeRadialKernel k Q c r

/-- Approach the imaginary quadratic coefficient from the right half-plane.
The dominator is independent of the approaching real part. -/
theorem shapeRadialIntegral_boundary_tendsto (k : ℕ) {Q d : ℝ}
    (hQ : 0 < Q) (hd : 0 < d) :
    Tendsto (fun δ : ℝ => shapeRadialIntegral k Q ((δ : ℂ) - Complex.I * d))
      (𝓝[Ici 0] 0) (𝓝 (shapeRadialIntegral k Q (-Complex.I * d))) := by
  unfold shapeRadialIntegral
  apply tendsto_integral_filter_of_dominated_convergence
    (fun r => ((min Q d / 2) ^ (k + 1))⁻¹ * shapeRadialMajorant k r)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (shapeRadialKernel_boundary_integrable k hQ hd hδ).aestronglyMeasurable.restrict
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact Filter.Eventually.of_forall fun r =>
      norm_shapeRadialKernel_le (by positivity) (shapeQuadratic_boundary_lower hQ hd hδ r)
  · exact ((shapeRadialMajorant_integrable k).const_mul _).integrableOn
  · apply Filter.Eventually.of_forall
    intro r
    have hn : shapeQuadratic Q (-Complex.I * d) r ≠ 0 := by
      simpa using shapeQuadratic_boundary_ne_zero hQ hd (δ := 0) (by rfl) r
    have hc : ContinuousAt (fun δ : ℝ =>
        shapeRadialKernel k Q ((δ : ℂ) - Complex.I * d) r) 0 := by
      have hden : ContinuousAt (fun δ : ℝ =>
          shapeQuadratic Q ((δ : ℂ) - Complex.I * d) r) 0 := by
        unfold shapeQuadratic
        exact continuousAt_const.add
          ((Complex.continuous_ofReal.continuousAt.sub continuousAt_const).mul continuousAt_const)
      exact continuousAt_const.div (hden.pow _) (by simpa using pow_ne_zero (k+1) hn)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

end
end IsingBulk.First
