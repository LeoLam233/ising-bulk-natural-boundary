import IsingBulk.First.RegularPoleDerivative
import IsingBulk.First.ActualAmplitudeNeighborhood

/-! Actual regular-chart density and pole jets, preserving every physical
source expression. Only required source-facing statements are generalized. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set Metric IsingBulk.Branch IsingBulk.First
open scoped Topology BigOperators

def actualLeadingAmplitude (a : RegularChartData) (n k : ℕ) (p : ℂ × (Fin n → ℝ)) : ℂ :=
  (actualSincFactor p.2:ℂ) * jointPoleLeadingNumerator
    (complexDensityRegular a.alpha) (complexDensityDenominator a.alpha) k
    (realShapeEmbedding n p) / ((n+1).factorial:ℂ)

def actualRemainderAmplitude (a : RegularChartData) (n k : ℕ) (p : ℂ × (Fin n → ℝ)) : ℂ :=
  (actualSincFactor p.2:ℂ) * jointPoleRemainder
    (complexDensityRegular a.alpha) (complexDensityDenominator a.alpha) k
    (realShapeEmbedding n p) / ((n+1).factorial:ℂ)

theorem actualLeadingAmplitude_continuousAt_center (a : RegularChartData) (n k : ℕ) :
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

theorem actualRemainderAmplitude_continuousAt_center (a : RegularChartData) (n k : ℕ) :
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
theorem actual_pole_amplitudes_locally_bounded (a : RegularChartData) (n k : ℕ) :
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
theorem actualLeadingAmplitude_eventually_continuousAt (a : RegularChartData) (n k : ℕ) :
    ∀ᶠ p : ℂ × (Fin n → ℝ) in 𝓝 (exp ((a.theta:ℂ)*I),0),
      ContinuousAt (actualLeadingAmplitude a n k) p := by
  have h := complex_analytic_real_shape_eventual_continuous
    (jointPoleLeadingNumerator_analyticAt (complexDensityRegular_analyticAt a (n+1))
      (complexDensityDenominator_analyticAt a (n+1)) k)
  filter_upwards [h] with p hp
  have he : ContinuousAt (fun q : ℂ × (Fin n → ℝ) => (actualSincFactor q.2:ℂ)) p :=
    (Complex.continuous_ofReal.comp ((actualSincFactor_continuous n).comp continuous_snd)).continuousAt
  exact (he.mul hp).div_const _

theorem actualRemainderAmplitude_eventually_continuousAt (a : RegularChartData) (n k : ℕ) :
    ∀ᶠ p : ℂ × (Fin n → ℝ) in 𝓝 (exp ((a.theta:ℂ)*I),0),
      ContinuousAt (actualRemainderAmplitude a n k) p := by
  have h := complex_analytic_real_shape_eventual_continuous
    (jointPoleRemainder_analyticAt (complexDensityRegular_analyticAt a (n+1))
      (complexDensityDenominator_analyticAt a (n+1)) k)
  filter_upwards [h] with p hp
  have he : ContinuousAt (fun q : ℂ × (Fin n → ℝ) => (actualSincFactor q.2:ℂ)) p :=
    (Complex.continuous_ofReal.comp ((actualSincFactor_continuous n).comp continuous_snd)).continuousAt
  exact (he.mul hp).div_const _

theorem actualDenominator_eventually_continuousAt (a : RegularChartData) (n : ℕ) :
    ∀ᶠ p : ℂ × (Fin n → ℝ) in 𝓝 (exp ((a.theta:ℂ)*I),0),
      ContinuousAt (fun q : ℂ × (Fin n → ℝ) => shapePoleDenominator q.1 a.alpha q.2) p := by
  exact complex_analytic_real_shape_eventual_continuous (complexDensityDenominator_analyticAt a (n+1))

end
end IsingBulk.First.Regular
