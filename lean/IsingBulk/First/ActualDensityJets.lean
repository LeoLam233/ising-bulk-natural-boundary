import IsingBulk.First.ActualPoleDerivative
import IsingBulk.First.ActualDensityBounds

/-! Actual highest-pole amplitude and lower-pole remainder. Their continuity
and boundedness include the physical pole itself; fixed real weights remain outside s derivatives. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter
open scoped Topology

def actualLeadingAmplitude (a : OrderedChartData) (n k : ℕ) (p : ℂ × (Fin n → ℝ)) : ℂ :=
  (actualSincFactor p.2:ℂ) * jointPoleLeadingNumerator
    (complexDensityRegular a.alpha) (complexDensityDenominator a.alpha) k
    (realShapeEmbedding n p) / ((n+1).factorial:ℂ)

def actualRemainderAmplitude (a : OrderedChartData) (n k : ℕ) (p : ℂ × (Fin n → ℝ)) : ℂ :=
  (actualSincFactor p.2:ℂ) * jointPoleRemainder
    (complexDensityRegular a.alpha) (complexDensityDenominator a.alpha) k
    (realShapeEmbedding n p) / ((n+1).factorial:ℂ)

theorem actualLeadingAmplitude_continuousAt_center (a : OrderedChartData) (n k : ℕ) :
    ContinuousAt (actualLeadingAmplitude a n k) (exp ((a.theta:ℂ)*I),0) := by
  have h := (jointPoleLeadingNumerator_analyticAt
    (complexDensityRegular_analyticAt a (n+1))
    (complexDensityDenominator_analyticAt a (n+1)) k).continuousAt
  rw [← realShapeEmbedding_center n (exp ((a.theta:ℂ)*I))] at h
  have hp := h.comp (realShapeEmbedding_continuous n).continuousAt
  have he : ContinuousAt (fun p : ℂ × (Fin n → ℝ) => (actualSincFactor p.2:ℂ))
      (exp ((a.theta:ℂ)*I),0) :=
    (Complex.continuous_ofReal.comp ((actualSincFactor_continuous n).comp continuous_snd)).continuousAt
  exact (he.mul hp).div_const _

theorem actualRemainderAmplitude_continuousAt_center (a : OrderedChartData) (n k : ℕ) :
    ContinuousAt (actualRemainderAmplitude a n k) (exp ((a.theta:ℂ)*I),0) := by
  have h := (jointPoleRemainder_analyticAt
    (complexDensityRegular_analyticAt a (n+1))
    (complexDensityDenominator_analyticAt a (n+1)) k).continuousAt
  rw [← realShapeEmbedding_center n (exp ((a.theta:ℂ)*I))] at h
  have hp := h.comp (realShapeEmbedding_continuous n).continuousAt
  have he : ContinuousAt (fun p : ℂ × (Fin n → ℝ) => (actualSincFactor p.2:ℂ))
      (exp ((a.theta:ℂ)*I),0) :=
    (Complex.continuous_ofReal.comp ((actualSincFactor_continuous n).comp continuous_snd)).continuousAt
  exact (he.mul hp).div_const _

theorem actualLeadingAmplitude_center (a : OrderedChartData) (n k : ℕ)
    (he : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    actualLeadingAmplitude a n k (exp ((a.theta:ℂ)*I),0) =
      (-1:ℂ)^k * (k.factorial:ℂ) * (a.K (n+1):ℂ) * a.Ds (n+1)^k := by
  have hB : complexDensityRegular a.alpha (exp ((a.theta:ℂ)*I),(0 : Fin (n+1) → ℂ)) /
      ((n+1).factorial:ℂ) = (a.K (n+1):ℂ) := by
    convert actualRegularFactor_center_eq_K a n he ha hb using 1
    rw [← complexDensityRegular_real_shape]
    simp only [shapeExtend_zero_exact, Pi.zero_apply, ofReal_zero]
    rfl
  unfold actualLeadingAmplitude
  rw [actualSincFactor_zero, ofReal_one, one_mul, realShapeEmbedding_center]
  unfold jointPoleLeadingNumerator poleLeadingNumerator
  rw [(actual_shape_denominator_hasDerivAt a n hb).deriv]
  linear_combination (-1:ℂ)^k * (k.factorial:ℂ) * a.Ds (n+1)^k * hB

/-- Both genuinely generated amplitudes have one common local bound before
varying s and the real shape coordinates. -/
theorem actual_pole_amplitudes_locally_bounded (a : OrderedChartData) (n k : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ p : ℂ × (Fin n → ℝ) in 𝓝 (exp ((a.theta:ℂ)*I),0),
      ‖actualLeadingAmplitude a n k p‖ ≤ M ∧ ‖actualRemainderAmplitude a n k p‖ ≤ M := by
  let c : ℂ × (Fin n → ℝ) := (exp ((a.theta:ℂ)*I),0)
  let M := ‖actualLeadingAmplitude a n k c‖ + ‖actualRemainderAmplitude a n k c‖ + 1
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  have hL := (actualLeadingAmplitude_continuousAt_center a n k).norm.tendsto.eventually
    (eventually_lt_nhds (show ‖actualLeadingAmplitude a n k c‖ < M by dsimp [M]; linarith [norm_nonneg (actualRemainderAmplitude a n k c)]))
  have hR := (actualRemainderAmplitude_continuousAt_center a n k).norm.tendsto.eventually
    (eventually_lt_nhds (show ‖actualRemainderAmplitude a n k c‖ < M by dsimp [M]; linarith [norm_nonneg (actualLeadingAmplitude a n k c)]))
  exact (hL.and hR).mono (fun _ h => ⟨h.1.le,h.2.le⟩)

/-- The actual highest-pole amplitude has the required fixed-shape scaling
limit, with the source radius already removed before parameter differentiation. -/
theorem actualLeadingAmplitude_scaled_limit (a : OrderedChartData) (n k : ℕ)
    (he : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) (tau : Fin n → ℝ) :
    Tendsto (fun lambda : ℝ => actualLeadingAmplitude a n k
      ((1+(lambda:ℂ)^2)*exp ((a.theta:ℂ)*I),fun j => lambda*tau j))
      (𝓝 0) (𝓝 ((-1:ℂ)^k*(k.factorial:ℂ)*(a.K (n+1):ℂ)*a.Ds (n+1)^k)) := by
  have hc : Continuous (fun lambda : ℝ =>
      ((1+(lambda:ℂ)^2)*exp ((a.theta:ℂ)*I),fun j => lambda*tau j)) := by fun_prop
  have ht : Tendsto (fun lambda : ℝ =>
      ((1+(lambda:ℂ)^2)*exp ((a.theta:ℂ)*I),fun j => lambda*tau j))
      (𝓝 0) (𝓝 (exp ((a.theta:ℂ)*I),(0 : Fin n → ℝ))) := by
    convert hc.continuousAt.tendsto using 1
    simp
    rfl
  have h := (actualLeadingAmplitude_continuousAt_center a n k).tendsto.comp ht
  simpa only [Function.comp_def, actualLeadingAmplitude_center a n k he ha hb] using h

end
end IsingBulk.First
