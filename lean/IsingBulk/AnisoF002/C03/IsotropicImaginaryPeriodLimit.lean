import IsingBulk.AnisoF002.C03.NegativeQuadraticPeriods
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# The isotropic scalar period: continuation on the original real plane

The frozen F002 local period has purely imaginary curvature.  Its
continuation from the fourth quadrant is justified here by a fixed
integrable majorant on the complete original independent-coordinate
plane.  No contour change or historical isotropic endpoint is used.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

def quadrantCurvature (D eps : ℝ) : ℂ := (eps : ℂ) - (D : ℂ) * Complex.I

theorem quadrantCurvature_re (D eps : ℝ) : (quadrantCurvature D eps).re = eps := by
  simp [quadrantCurvature]

theorem quadrant_denominator_bound {τ D eps q : ℝ}
    (he : 0 ≤ eps) (hq : 0 ≤ q) :
    τ + D * q ≤ 2 * ‖(τ : ℂ) + quadrantCurvature D eps * (q : ℂ)‖ := by
  let z : ℂ := (τ : ℂ) + quadrantCurvature D eps * (q : ℂ)
  have hr := Complex.re_le_norm z
  have hi : -z.im ≤ ‖z‖ := (neg_le_abs z.im).trans (Complex.abs_im_le_norm z)
  have hrval : z.re = τ + eps * q := by simp [z, quadrantCurvature]
  have hival : z.im = -D * q := by simp [z, quadrantCurvature]
  rw [hrval] at hr
  rw [hival] at hi
  have hep := mul_nonneg he hq
  change τ + D * q ≤ 2 * ‖z‖
  linarith

theorem quadrant_denominator_ne_zero {τ D eps q : ℝ}
    (hτ : 0 < τ) (hD : 0 < D) (he : 0 ≤ eps) (hq : 0 ≤ q) :
    (τ : ℂ) + quadrantCurvature D eps * (q : ℂ) ≠ 0 := by
  intro hz
  have hh := quadrant_denominator_bound (τ := τ) (D := D) he hq
  rw [hz, norm_zero, mul_zero] at hh
  have hp := mul_nonneg hD.le hq
  linarith

theorem quadrant_period_norm_bound {d k : ℕ} {τ D eps : ℝ}
    (hτ : 0 < τ) (hD : 0 < D) (he : 0 ≤ eps) (v : constrainedPlane d) :
    ‖quadraticPeriodIntegrand d k τ (quadrantCurvature D eps) v‖ ≤
      (2 : ℝ) ^ k * ‖quadraticPeriodIntegrand d k τ (D : ℂ) v‖ := by
  have hq : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  have hden := quadrant_denominator_bound (τ := τ) (D := D) he hq
  have hden0 := norm_pos_iff.mpr (quadrant_denominator_ne_zero hτ hD he hq)
  have hr : 0 < τ + D * ‖v‖ ^ 2 := by positivity
  have hreal : ‖(τ : ℂ) + (D : ℂ) * (‖v‖ ^ 2 : ℝ)‖ = τ + D * ‖v‖ ^ 2 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
  simp only [quadraticPeriodIntegrand, norm_div, norm_pow, hreal]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos hden0 _) (pow_pos hr _)).mpr
  calc
    _ ≤ ‖(planeVandermonde v : ℂ)‖ *
        (2 * ‖(τ : ℂ) + quadrantCurvature D eps * (‖v‖ ^ 2 : ℝ)‖) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hden k) (norm_nonneg _)
    _ = _ := by rw [mul_pow]; ring

theorem continuous_quadrant_period {d k : ℕ} {τ D eps : ℝ}
    (hτ : 0 < τ) (hD : 0 < D) (he : 0 ≤ eps) :
    Continuous (quadraticPeriodIntegrand d k τ (quadrantCurvature D eps)) := by
  unfold quadraticPeriodIntegrand
  apply Continuous.div
  · exact Complex.continuous_ofReal.comp (continuous_planeVandermonde d)
  · fun_prop
  · intro v
    exact pow_ne_zero _ (quadrant_denominator_ne_zero hτ hD he (sq_nonneg ‖v‖))

theorem quadrant_period_pointwise_limit {d k : ℕ} {τ D : ℝ}
    (hτ : 0 < τ) (hD : 0 < D) (v : constrainedPlane d) :
    Tendsto (fun eps : ℝ => quadraticPeriodIntegrand d k τ (quadrantCurvature D eps) v)
      (𝓝[>] 0) (𝓝 (quadraticPeriodIntegrand d k τ (quadrantCurvature D 0) v)) := by
  have hc : ContinuousAt
      (fun eps : ℝ => quadraticPeriodIntegrand d k τ (quadrantCurvature D eps) v) 0 := by
    unfold quadraticPeriodIntegrand
    apply ContinuousAt.div continuousAt_const
    · unfold quadrantCurvature
      fun_prop
    · exact pow_ne_zero _ (quadrant_denominator_ne_zero hτ hD le_rfl (sq_nonneg ‖v‖))
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem quadrant_period_integrable {d k : ℕ} {τ D eps : ℝ}
    (hτ : 0 < τ) (hD : 0 < D) (he : 0 ≤ eps)
    (hi : Integrable (quadraticPeriodIntegrand d k τ (D : ℂ)) (independentMeasure d)) :
    Integrable (quadraticPeriodIntegrand d k τ (quadrantCurvature D eps))
      (independentMeasure d) := by
  apply (hi.norm.const_mul ((2 : ℝ) ^ k)).mono'
  · exact (continuous_quadrant_period hτ hD he).aestronglyMeasurable
  · exact Eventually.of_forall (quadrant_period_norm_bound hτ hD he)

theorem quadrant_period_integral_limit {d k : ℕ} {τ D : ℝ}
    (hτ : 0 < τ) (hD : 0 < D)
    (hi : Integrable (quadraticPeriodIntegrand d k τ (D : ℂ)) (independentMeasure d)) :
    Tendsto (fun eps : ℝ => ∫ v,
      quadraticPeriodIntegrand d k τ (quadrantCurvature D eps) v ∂independentMeasure d)
      (𝓝[>] 0) (𝓝 (∫ v,
        quadraticPeriodIntegrand d k τ (quadrantCurvature D 0) v ∂independentMeasure d)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun v => (2 : ℝ) ^ k * ‖quadraticPeriodIntegrand d k τ (D : ℂ) v‖)
  · filter_upwards [self_mem_nhdsWithin] with eps he
    exact (continuous_quadrant_period hτ hD he.le).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with eps he
    exact Eventually.of_forall (quadrant_period_norm_bound hτ hD he.le)
  · exact hi.norm.const_mul _
  · exact Eventually.of_forall (quadrant_period_pointwise_limit hτ hD)

end
end IsingBulk.AnisoF002.NegativeHT.Angular
