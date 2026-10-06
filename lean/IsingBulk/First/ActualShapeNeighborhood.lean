import IsingBulk.First.ActualShapeAmplitude
import IsingBulk.First.ActualAmplitudeNeighborhood

/-! One actual radial-shape neighborhood supports continuity and uniform
bounds for both generated pole amplitudes and the physical denominator. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex Filter Metric
open scoped Topology

theorem intrinsic_actual_eventual_continuity {n : ℕ} (a : OrderedChartData) (k : ℕ) :
    ∀ᶠ p : ℝ × ShapeSpace n in 𝓝 (0,0),
      ContinuousAt (intrinsicLeadingAmplitude a k) p ∧
      ContinuousAt (intrinsicRemainderAmplitude a k) p ∧
      ContinuousAt (fun q : ℝ × ShapeSpace n => actualShapeDenominator a q.1 q.2) p := by
  have ht : Tendsto (@intrinsicRadialEmbedding n a) (𝓝 (0,0))
      (𝓝 (exp ((a.theta:ℂ)*I),0)) := by
    simpa only [intrinsicRadialEmbedding_zero] using
      (intrinsicRadialEmbedding_continuous (n := n) a).tendsto (0,0)
  filter_upwards [ht.eventually (actualLeadingAmplitude_eventually_continuousAt a n k),
    ht.eventually (actualRemainderAmplitude_eventually_continuousAt a n k),
    ht.eventually (actualDenominator_eventually_continuousAt a n)] with p hL hR hD
  exact ⟨hL.comp (intrinsicRadialEmbedding_continuous a).continuousAt,
    hR.comp (intrinsicRadialEmbedding_continuous a).continuousAt,
    hD.comp (intrinsicRadialEmbedding_continuous a).continuousAt⟩

/-- The neighborhood and bound are chosen before varying either radial
parameter or shape. No boundedness or continuity estimate is assumed. -/
theorem intrinsic_actual_uniform_neighborhood {n : ℕ} (a : OrderedChartData) (k : ℕ) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ epsilon : ℝ, ∀ x : ShapeSpace n,
      |epsilon| < r → ‖x‖ < r →
      ContinuousAt (intrinsicLeadingAmplitude a k) (epsilon,x) ∧
      ContinuousAt (intrinsicRemainderAmplitude a k) (epsilon,x) ∧
      ContinuousAt (fun q : ℝ × ShapeSpace n => actualShapeDenominator a q.1 q.2) (epsilon,x) ∧
      ‖intrinsicLeadingAmplitude a k (epsilon,x)‖ ≤ M ∧
      ‖intrinsicRemainderAmplitude a k (epsilon,x)‖ ≤ M := by
  obtain ⟨M,hM,hb⟩ := intrinsic_pole_amplitudes_locally_bounded (n := n) a k
  have hh := (intrinsic_actual_eventual_continuity (n := n) a k).and hb
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨r,M,hr,hM,?_⟩
  intro epsilon x he hx
  have hm : (epsilon,x) ∈ ball (0,(0:ShapeSpace n)) r := by
    rw [mem_ball, dist_eq_norm]
    change max ‖epsilon-0‖ ‖x-0‖ < r
    simpa only [sub_zero, Real.norm_eq_abs, max_lt_iff] using And.intro he hx
  have hp := hs hm
  exact ⟨hp.1.1,hp.1.2.1,hp.1.2.2,hp.2.1,hp.2.2⟩

end
end IsingBulk.First
