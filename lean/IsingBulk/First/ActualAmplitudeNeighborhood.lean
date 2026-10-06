import IsingBulk.First.ActualDensityJets

/-! Local continuity of the actual amplitudes throughout a fixed neighborhood,
including the zero set of the physical pole denominator. -/
namespace IsingBulk.First
noncomputable section
open Complex Filter
open scoped Topology

theorem complex_analytic_real_shape_eventual_continuous {n : ℕ}
    {F : ℂ × (Fin (n+1) → ℂ) → ℂ} {s : ℂ}
    (hF : AnalyticAt ℂ F (s,0)) :
    ∀ᶠ p : ℂ × (Fin n → ℝ) in 𝓝 (s,0),
      ContinuousAt (fun q => F (realShapeEmbedding n q)) p := by
  have hm : Tendsto (realShapeEmbedding n) (𝓝 (s,(0 : Fin n → ℝ)))
      (𝓝 (s,(0 : Fin (n+1) → ℂ))) := by
    simpa only [realShapeEmbedding_center] using
      (realShapeEmbedding_continuous n).continuousAt.tendsto (x := (s,0))
  filter_upwards [hm.eventually hF.eventually_analyticAt] with p hp
  exact hp.continuousAt.comp (realShapeEmbedding_continuous n).continuousAt

theorem actualLeadingAmplitude_eventually_continuousAt (a : OrderedChartData) (n k : ℕ) :
    ∀ᶠ p : ℂ × (Fin n → ℝ) in 𝓝 (exp ((a.theta:ℂ)*I),0),
      ContinuousAt (actualLeadingAmplitude a n k) p := by
  have h := complex_analytic_real_shape_eventual_continuous
    (jointPoleLeadingNumerator_analyticAt (complexDensityRegular_analyticAt a (n+1))
      (complexDensityDenominator_analyticAt a (n+1)) k)
  filter_upwards [h] with p hp
  have he : ContinuousAt (fun q : ℂ × (Fin n → ℝ) => (actualSincFactor q.2:ℂ)) p :=
    (Complex.continuous_ofReal.comp ((actualSincFactor_continuous n).comp continuous_snd)).continuousAt
  exact (he.mul hp).div_const _

theorem actualRemainderAmplitude_eventually_continuousAt (a : OrderedChartData) (n k : ℕ) :
    ∀ᶠ p : ℂ × (Fin n → ℝ) in 𝓝 (exp ((a.theta:ℂ)*I),0),
      ContinuousAt (actualRemainderAmplitude a n k) p := by
  have h := complex_analytic_real_shape_eventual_continuous
    (jointPoleRemainder_analyticAt (complexDensityRegular_analyticAt a (n+1))
      (complexDensityDenominator_analyticAt a (n+1)) k)
  filter_upwards [h] with p hp
  have he : ContinuousAt (fun q : ℂ × (Fin n → ℝ) => (actualSincFactor q.2:ℂ)) p :=
    (Complex.continuous_ofReal.comp ((actualSincFactor_continuous n).comp continuous_snd)).continuousAt
  exact (he.mul hp).div_const _

theorem actualDenominator_eventually_continuousAt (a : OrderedChartData) (n : ℕ) :
    ∀ᶠ p : ℂ × (Fin n → ℝ) in 𝓝 (exp ((a.theta:ℂ)*I),0),
      ContinuousAt (fun q : ℂ × (Fin n → ℝ) => shapePoleDenominator q.1 a.alpha q.2) p := by
  exact complex_analytic_real_shape_eventual_continuous (complexDensityDenominator_analyticAt a (n+1))

end
end IsingBulk.First
