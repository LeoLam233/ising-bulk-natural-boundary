import IsingBulk.First.ActualShapeDenominator
import IsingBulk.First.ActualDensityJets

/-! Actual pole amplitudes pulled back to the intrinsic zero-sum Euclidean
shape space. Their limits and local bounds retain the source normalization. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex Filter
open scoped Topology

def intrinsicRadialEmbedding {n : ℕ} (a : OrderedChartData)
    (p : ℝ × ShapeSpace n) : ℂ × (Fin n → ℝ) :=
  (radialParameter a.theta p.1,intrinsicShapeCoordinates p.2)

theorem intrinsicRadialEmbedding_continuous {n : ℕ} (a : OrderedChartData) :
    Continuous (@intrinsicRadialEmbedding n a) := by
  apply Continuous.prodMk _ ((intrinsicShapeCoordinates_continuous n).comp continuous_snd)
  unfold radialParameter
  fun_prop

@[simp] theorem intrinsicRadialEmbedding_zero {n : ℕ} (a : OrderedChartData) :
    intrinsicRadialEmbedding a (0,(0:ShapeSpace n)) = (exp ((a.theta:ℂ)*I),0) := by
  change ((radialParameter a.theta 0),intrinsicShapeCoordinates (0:ShapeSpace n)) = _
  have hz : intrinsicShapeCoordinates (0:ShapeSpace n) = 0 := rfl
  simp [radialParameter, hz]

def intrinsicLeadingAmplitude {n : ℕ} (a : OrderedChartData) (k : ℕ)
    (p : ℝ × ShapeSpace n) : ℂ :=
  actualLeadingAmplitude a n k (intrinsicRadialEmbedding a p)

def intrinsicRemainderAmplitude {n : ℕ} (a : OrderedChartData) (k : ℕ)
    (p : ℝ × ShapeSpace n) : ℂ :=
  actualRemainderAmplitude a n k (intrinsicRadialEmbedding a p)

theorem intrinsicLeadingAmplitude_continuousAt_zero {n : ℕ} (a : OrderedChartData) (k : ℕ) :
    ContinuousAt (@intrinsicLeadingAmplitude n a k) (0,0) := by
  have h := actualLeadingAmplitude_continuousAt_center a n k
  rw [← intrinsicRadialEmbedding_zero (n := n) a] at h
  exact h.comp (intrinsicRadialEmbedding_continuous a).continuousAt

theorem intrinsicRemainderAmplitude_continuousAt_zero {n : ℕ} (a : OrderedChartData) (k : ℕ) :
    ContinuousAt (@intrinsicRemainderAmplitude n a k) (0,0) := by
  have h := actualRemainderAmplitude_continuousAt_center a n k
  rw [← intrinsicRadialEmbedding_zero (n := n) a] at h
  exact h.comp (intrinsicRadialEmbedding_continuous a).continuousAt

theorem intrinsicLeadingAmplitude_zero {n : ℕ} (a : OrderedChartData) (k : ℕ)
    (he : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    intrinsicLeadingAmplitude a k (0,(0:ShapeSpace n)) =
      (-1:ℂ)^k*(k.factorial:ℂ)*(a.K (n+1):ℂ)*a.Ds (n+1)^k := by
  rw [intrinsicLeadingAmplitude, intrinsicRadialEmbedding_zero]
  exact actualLeadingAmplitude_center a n k he ha hb

theorem intrinsicLeadingAmplitude_scale_limit {n : ℕ} (a : OrderedChartData) (k : ℕ)
    (he : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) (x : ShapeSpace n) :
    Tendsto (fun lam : ℝ => intrinsicLeadingAmplitude a k (lam^2,lam • x))
      (𝓝[>] 0) (𝓝 ((-1:ℂ)^k*(k.factorial:ℂ)*(a.K (n+1):ℂ)*a.Ds (n+1)^k)) := by
  have hp : Tendsto (fun lam : ℝ => (lam^2,lam • x)) (𝓝[>] 0) (𝓝 (0,0)) := by
    have hc : Continuous (fun lam : ℝ => (lam^2,lam • x)) := by fun_prop
    simpa using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have h := (intrinsicLeadingAmplitude_continuousAt_zero a k).tendsto.comp hp
  simpa only [Function.comp_def, intrinsicLeadingAmplitude_zero a k he ha hb] using h

theorem intrinsic_pole_amplitudes_locally_bounded {n : ℕ} (a : OrderedChartData) (k : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ p : ℝ × ShapeSpace n in 𝓝 (0,0),
      ‖intrinsicLeadingAmplitude a k p‖ ≤ M ∧ ‖intrinsicRemainderAmplitude a k p‖ ≤ M := by
  obtain ⟨M,hM,h⟩ := actual_pole_amplitudes_locally_bounded a n k
  refine ⟨M,hM,?_⟩
  have ht : Tendsto (@intrinsicRadialEmbedding n a) (𝓝 (0,0))
      (𝓝 (exp ((a.theta:ℂ)*I),0)) := by
    simpa only [intrinsicRadialEmbedding_zero] using
      (intrinsicRadialEmbedding_continuous (n := n) a).tendsto (0,0)
  exact ht.eventually h

end
end IsingBulk.First
