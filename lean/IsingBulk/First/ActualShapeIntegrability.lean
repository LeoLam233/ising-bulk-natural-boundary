import IsingBulk.First.ActualShapeNeighborhood
import IsingBulk.First.ShapeCutoffBounds

/-! Absolute integrability of the actual highest-pole shape density at each
positive radial parameter, before splitting the integrated derivative. -/
namespace IsingBulk.First
noncomputable section
open Complex MeasureTheory Set Filter Metric

theorem actual_leading_shape_integrable {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) (a : OrderedChartData)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → (∀ x, ‖chi x‖ ≤ 1) → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      ∀ epsilon ∈ Ioo 0 R,
        Integrable (fun x => (shapeVandermondeSq x:ℂ)*chi x*intrinsicLeadingAmplitude a k (epsilon,x)/
          (actualShapeDenominator a epsilon x)^(k+1)) := by
  obtain ⟨rA,M,hrA,hM,hA⟩ := intrinsic_actual_uniform_neighborhood (n := n) a k
  obtain ⟨c,rD,hc,hrD,hD⟩ := actualShapeDenominator_uniform_lower (n := n) a hb
  let R := min rA rD
  refine ⟨R,lt_min hrA hrD,?_⟩
  intro chi hchi hchib hchis epsilon he
  have hdata (x : ShapeSpace n) (hx : x ∈ ball 0 R) :=
    hA epsilon x (by rw [abs_of_pos he.1]; exact he.2.trans_le (min_le_left _ _))
      ((by simpa only [mem_ball, dist_zero_right] using hx : ‖x‖ < R).trans_le (min_le_left _ _))
  exact shape_cutoff_integrable_positive_gap hn hdegree
    (fun x => intrinsicLeadingAmplitude a k (epsilon,x))
    (actualShapeDenominator a epsilon) chi R he.1 hM.le hc hchi hchib hchis
    (fun x hx => ((hdata x hx).1.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
    (fun x hx => ((hdata x hx).2.2.1.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
    (fun x hx => (hdata x hx).2.2.2.1)
    (fun x hx => hD epsilon x he.1 (he.2.trans_le (min_le_right _ _))
      ((by simpa only [mem_ball, dist_zero_right] using hx : ‖x‖ < R).trans_le (min_le_right _ _)))

end
end IsingBulk.First
