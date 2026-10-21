import IsingBulk.First.RegularScaledDenominator
import IsingBulk.First.RegularDensityExpansion
import IsingBulk.First.ActualShapeDerivative

/-! Actual regular-chart shape scaling and generated physical amplitudes.
All source denominators, shape measures and parameter derivatives are literal. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex MeasureTheory Filter Set Metric IsingBulk.Branch IsingBulk.First
open scoped Topology BigOperators

def actualShapeDenominator {n : ℕ} (a : RegularChartData) (epsilon : ℝ)
    (x : ShapeSpace n) : ℂ :=
  shapePoleDenominator (radialParameter a.theta epsilon) a.alpha (intrinsicShapeCoordinates x)

/-- One positive constant and one neighborhood control all source parameters
and shapes in the support ball. -/
theorem actualShapeDenominator_uniform_lower {n : ℕ} (a : RegularChartData)
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
theorem actualShapeDenominator_scale_limit {n : ℕ} (a : RegularChartData)
    (hb : Complex.exp (-(n+1:ℂ)*(a.beta:ℂ)*Complex.I) = 1) (x : ShapeSpace n) :
    Tendsto (fun lam : ℝ => actualShapeDenominator a (lam^2) (lam • x)/(lam:ℂ)^2)
      (𝓝[>] 0) (𝓝 ((a.Q (n+1):ℂ)-Complex.I*(a.d:ℂ)*(‖x‖:ℂ)^2)) := by
  have h := actual_shape_denominator_scale_limit a (intrinsicShapeCoordinates x) hb
  have hs : (∑ j, ((shapeExtend (intrinsicShapeCoordinates x) j:ℝ):ℂ)^2) = (‖x‖:ℂ)^2 := by
    exact_mod_cast intrinsic_shape_square_sum x
  simpa only [actualShapeDenominator, intrinsicShapeCoordinates_smul, hs] using h

def intrinsicRadialEmbedding {n : ℕ} (a : RegularChartData)
    (p : ℝ × ShapeSpace n) : ℂ × (Fin n → ℝ) :=
  (radialParameter a.theta p.1,intrinsicShapeCoordinates p.2)

theorem intrinsicRadialEmbedding_continuous {n : ℕ} (a : RegularChartData) :
    Continuous (@intrinsicRadialEmbedding n a) := by
  apply Continuous.prodMk _ ((intrinsicShapeCoordinates_continuous n).comp continuous_snd)
  unfold radialParameter
  fun_prop

@[simp] theorem intrinsicRadialEmbedding_zero {n : ℕ} (a : RegularChartData) :
    intrinsicRadialEmbedding a (0,(0:ShapeSpace n)) = (exp ((a.theta:ℂ)*I),0) := by
  change ((radialParameter a.theta 0),intrinsicShapeCoordinates (0:ShapeSpace n)) = _
  have hz : intrinsicShapeCoordinates (0:ShapeSpace n) = 0 := rfl
  simp [radialParameter, hz]

def intrinsicLeadingAmplitude {n : ℕ} (a : RegularChartData) (k : ℕ)
    (p : ℝ × ShapeSpace n) : ℂ :=
  actualLeadingAmplitude a n k (intrinsicRadialEmbedding a p)

def intrinsicRemainderAmplitude {n : ℕ} (a : RegularChartData) (k : ℕ)
    (p : ℝ × ShapeSpace n) : ℂ :=
  actualRemainderAmplitude a n k (intrinsicRadialEmbedding a p)

theorem intrinsicLeadingAmplitude_continuousAt_zero {n : ℕ} (a : RegularChartData) (k : ℕ) :
    ContinuousAt (@intrinsicLeadingAmplitude n a k) (0,0) := by
  have h := actualLeadingAmplitude_continuousAt_center a n k
  rw [← intrinsicRadialEmbedding_zero (n := n) a] at h
  exact h.comp (intrinsicRadialEmbedding_continuous a).continuousAt

theorem intrinsicRemainderAmplitude_continuousAt_zero {n : ℕ} (a : RegularChartData) (k : ℕ) :
    ContinuousAt (@intrinsicRemainderAmplitude n a k) (0,0) := by
  have h := actualRemainderAmplitude_continuousAt_center a n k
  rw [← intrinsicRadialEmbedding_zero (n := n) a] at h
  exact h.comp (intrinsicRadialEmbedding_continuous a).continuousAt

theorem intrinsic_pole_amplitudes_locally_bounded {n : ℕ} (a : RegularChartData) (k : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ p : ℝ × ShapeSpace n in 𝓝 (0,0),
      ‖intrinsicLeadingAmplitude a k p‖ ≤ M ∧ ‖intrinsicRemainderAmplitude a k p‖ ≤ M := by
  obtain ⟨M,hM,h⟩ := actual_pole_amplitudes_locally_bounded a n k
  refine ⟨M,hM,?_⟩
  have ht : Tendsto (@intrinsicRadialEmbedding n a) (𝓝 (0,0))
      (𝓝 (exp ((a.theta:ℂ)*I),0)) := by
    simpa only [intrinsicRadialEmbedding_zero] using
      (intrinsicRadialEmbedding_continuous (n := n) a).tendsto (0,0)
  exact ht.eventually h

theorem intrinsic_actual_eventual_continuity {n : ℕ} (a : RegularChartData) (k : ℕ) :
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
theorem intrinsic_actual_uniform_neighborhood {n : ℕ} (a : RegularChartData) (k : ℕ) :
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

def intrinsicPostMeanDerivative {n : ℕ} (a : RegularChartData) (k : ℕ)
    (epsilon : ℝ) (x : ShapeSpace n) : ℂ :=
  (deriv^[k] (fun s => postMeanDensity s a.alpha (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ)))
    (radialParameter a.theta epsilon)

theorem intrinsic_postMean_derivative_expansion {n : ℕ} (a : RegularChartData) (k : ℕ)
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
end IsingBulk.First.Regular
