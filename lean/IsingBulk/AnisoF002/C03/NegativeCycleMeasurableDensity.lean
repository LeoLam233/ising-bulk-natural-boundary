import IsingBulk.AnisoF002.C03.NegativeOuterCycleControl
import IsingBulk.AnisoF002.C03.NegativeLocalPoleMeasurable
import IsingBulk.AnisoF002.C03.NegativeInnerRemainder

/-!
# Measurability of the literal complete real-cycle density

Only the actual jointly continuous local numerator and phase are used.
The exponential quotient is Borel measurable even at its totalized zero
denominator; subsequent physical disk estimates separately exclude it.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology

theorem phaseSiteFactor_measurable : Measurable phaseSiteFactor := by
  have he : Measurable (fun z : ℂ => Complex.exp (-z)) :=
    Complex.continuous_exp.measurable.comp measurable_neg
  exact (measurable_const.add he).div (measurable_const.sub he)

theorem exists_actual_real_density_measurable {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ r : ℝ, 0 < r ∧ ∀ n : ℕ, 0 < n → ∀ t ∈ Metric.ball (0 : ℂ) r,
      Measurable (realNegativeDensity b B φ n t) := by
  obtain ⟨r, hr, hJ⟩ := exists_actual_joint_real_factor_control hb hB hφ hπ hBi hbsq
  refine ⟨r, hr, ?_⟩
  intro n hn t ht
  let H : ℂ → (Fin n → ℝ) → ℂ := fun u q =>
    completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 u (fun i => (q i : ℂ))
  let F : ℂ → (Fin n → ℝ) → ℂ := fun u q => realPhaseAverage B φ n q u
  have hHc : ContinuousOn (Function.uncurry H) {p : ℂ × (Fin n → ℝ) | p.1 ∈ Metric.ball 0 r} := by
    change ContinuousOn (fun p : ℂ × (Fin n → ℝ) =>
      completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 p.1 (fun i => (p.2 i : ℂ))) _
    exact (hJ n).1
  have hFc : ContinuousOn (Function.uncurry F) {p : ℂ × (Fin n → ℝ) | p.1 ∈ Metric.ball 0 r} := by
    change ContinuousOn (fun p : ℂ × (Fin n → ℝ) => realPhaseAverage B φ n p.2 p.1) _
    exact (hJ n).2.1
  have hHm : Measurable (diskKernelExtension r H t) :=
    (diskKernelExtension_measurable hHc).comp (measurable_const.prodMk measurable_id)
  have hFm : Measurable (diskKernelExtension r F t) :=
    (diskKernelExtension_measurable hFc).comp (measurable_const.prodMk measurable_id)
  have hm : Measurable (fun q : Fin n → ℝ => diskKernelExtension r H t q *
      phaseSiteFactor ((n : ℂ) * ((φ : ℂ) * Complex.I) + (n : ℂ) * diskKernelExtension r F t q)) :=
    hHm.mul (phaseSiteFactor_measurable.comp (measurable_const.add (measurable_const.mul hFm)))
  have heq : (fun q : Fin n → ℝ => diskKernelExtension r H t q *
      phaseSiteFactor ((n : ℂ) * ((φ : ℂ) * Complex.I) + (n : ℂ) * diskKernelExtension r F t q)) =
      realNegativeDensity b B φ n t := by
    funext q
    rw [diskKernelExtension_eq H ht, diskKernelExtension_eq F ht]
    change H t q * phaseSiteFactor ((n : ℂ) * ((φ : ℂ) * Complex.I) +
      (n : ℂ) * realPhaseAverage B φ n q t) = realNegativeDensity b B φ n t q
    rw [← realPhaseTotal_eq_average B φ hn q t]
    rfl
  rw [← heq]
  exact hm

end
end IsingBulk.AnisoF002.NegativeHT
