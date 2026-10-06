import IsingBulk.First.ActualDensityExpansion
import IsingBulk.First.ActualShapeAmplitude

/-! Literal normalized post-mean parameter derivatives on one positive-radial
shape neighborhood, with pole exclusion supplied by the actual nonlinear gap. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex Filter Metric
open scoped Topology

def intrinsicPostMeanDerivative {n : ℕ} (a : OrderedChartData) (k : ℕ)
    (epsilon : ℝ) (x : ShapeSpace n) : ℂ :=
  (deriv^[k] (fun s => postMeanDensity s a.alpha (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ)))
    (radialParameter a.theta epsilon)

theorem intrinsic_postMean_derivative_expansion {n : ℕ} (a : OrderedChartData) (k : ℕ)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ epsilon : ℝ, ∀ x : ShapeSpace n,
      0 < epsilon → epsilon < r → ‖x‖ < r →
      intrinsicPostMeanDerivative a k epsilon x =
        2*(Real.pi:ℂ)*(shapeVandermondeSq x:ℂ)*
          (intrinsicLeadingAmplitude a k (epsilon,x)/(actualShapeDenominator a epsilon x)^(k+1)+
            intrinsicRemainderAmplitude a k (epsilon,x)/(actualShapeDenominator a epsilon x)^k) := by
  obtain ⟨rE,hrE,hE⟩ := actual_postMean_derivative_expansion a n k
  have ht : Tendsto (@intrinsicRadialEmbedding n a) (𝓝 (0,0))
      (𝓝 (exp ((a.theta:ℂ)*I),0)) := by
    simpa only [intrinsicRadialEmbedding_zero] using
      (intrinsicRadialEmbedding_continuous (n := n) a).tendsto (0,0)
  have hevent := ht.eventually (ball_mem_nhds (exp ((a.theta:ℂ)*I),(0:Fin n → ℝ)) hrE)
  obtain ⟨r0,hr0,h0⟩ := Metric.mem_nhds_iff.mp hevent
  obtain ⟨c,rD,hc,hrD,hD⟩ := actualShapeDenominator_uniform_lower (n := n) a hb
  refine ⟨min r0 rD,lt_min hr0 hrD,?_⟩
  intro epsilon x he her hxr
  have hm : (epsilon,x) ∈ ball (0,(0:ShapeSpace n)) r0 := by
    rw [mem_ball, dist_eq_norm]
    change max ‖epsilon-0‖ ‖x-0‖ < r0
    simp only [sub_zero, Real.norm_eq_abs, abs_of_pos he, max_lt_iff]
    exact ⟨her.trans_le (min_le_left _ _),hxr.trans_le (min_le_left _ _)⟩
  have hgap := hD epsilon x he (her.trans_le (min_le_right _ _)) (hxr.trans_le (min_le_right _ _))
  have hne : actualShapeDenominator a epsilon x ≠ 0 := by
    intro hz
    rw [hz,norm_zero] at hgap
    have hp : 0 < c*(epsilon+‖x‖^2) := mul_pos hc (by positivity)
    linarith
  have h := hE (radialParameter a.theta epsilon) (intrinsicShapeCoordinates x) (h0 hm) hne
  simpa only [intrinsicPostMeanDerivative, intrinsicLeadingAmplitude, intrinsicRemainderAmplitude,
    intrinsicRadialEmbedding, actualShapeDenominator, shapeVandermondeSq,
    shapeExtend_intrinsicShapeCoordinates, ofReal_pow] using h

end
end IsingBulk.First
