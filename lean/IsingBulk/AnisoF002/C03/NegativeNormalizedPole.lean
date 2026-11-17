import IsingBulk.AnisoF002.C03.NegativePoleAngularBounds
import IsingBulk.AnisoF002.C03.NegativeScaledRadialIntegral

/-!
# Normalized beta coordinates for the actual compact pole

All functions here are literal integrals of the constructed physical
pole and its complete residue density.  Measurability follows from the
proved compact-ball continuity; no regularity of arbitrary values of a
chosen local analytic germ outside its ball is assumed.
-/

namespace IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
noncomputable section
open MeasureTheory Set Angular

variable {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {d : ℕ}
variable (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)

def radialScale (_p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp) : ℝ :=
  2 * ((d + 1 : ℕ) : ℝ) * windingTau (d + 1) /
    (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ)) (Real.cos φ) (Real.sin φ)).re

def radialRadius (x : ℝ) : ℝ := Real.sqrt (p.radialScale * x)

def compactAngularMean (k : ℕ) (R r : ℝ) : ℂ :=
  ∫ θ : AngularSphere d,
    (Metric.closedBall (0 : constrainedPlane d) R).indicator (p.realPoleFactor k)
      (r • θ.val) ∂angularLaw d

def normalizedPoleError (k : ℕ) (R x : ℝ) : ℂ :=
  (windingTau (d + 1) : ℂ) ^ k *
    (p.compactAngularMean k R (p.radialRadius x) -
      1 / angularQuadraticPole d (windingTau (d + 1))
        (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
          (Real.cos φ) (Real.sin φ)) (p.radialRadius x) ^ k)

theorem radialScale_pos : 0 < p.radialScale := by
  have hh := p.curvature_re
  have ht := windingTau_pos (d + 1) (by omega)
  unfold radialScale
  positivity

theorem radialRadius_nonneg (x : ℝ) : 0 ≤ p.radialRadius x := Real.sqrt_nonneg _

theorem radialRadius_sq {x : ℝ} (hx : 0 ≤ x) :
    p.radialRadius x ^ 2 = p.radialScale * x :=
  Real.sq_sqrt (mul_nonneg p.radialScale_pos.le hx)

theorem radialRadius_parameter {x : ℝ} (hx : 0 ≤ x) :
    (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)).re * p.radialRadius x ^ 2 /
        (2 * ((d + 1 : ℕ) : ℝ) * windingTau (d + 1)) = x := by
  have hn : (((d + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have ht := (windingTau_pos (d + 1) (by omega)).ne'
  have hh : (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)).re ≠ 0 := by have he := p.curvature_re; linarith
  rw [p.radialRadius_sq hx]
  unfold radialScale
  field_simp

theorem radialRadius_denominator {x : ℝ} (hx : 0 ≤ x) :
    windingTau (d + 1) +
      (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
        (Real.cos φ) (Real.sin φ)).re * p.radialRadius x ^ 2 /
          (2 * ((d + 1 : ℕ) : ℝ)) = windingTau (d + 1) * (1 + x) := by
  have ht := (windingTau_pos (d + 1) (by omega)).ne'
  calc
    _ = windingTau (d + 1) * (1 +
      (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
        (Real.cos φ) (Real.sin φ)).re * p.radialRadius x ^ 2 /
          (2 * ((d + 1 : ℕ) : ℝ) * windingTau (d + 1))) := by
      field_simp
    _ = _ := by rw [p.radialRadius_parameter hx]

theorem compactAngularMean_inside (k : ℕ) {R r : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    p.compactAngularMean k R r = p.angularPoleMean k r := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro θ
  have hθ : ‖θ.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  apply indicator_of_mem
  simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hr,
    hθ, mul_one] using hrR

theorem compactAngularMean_outside (k : ℕ) {R r : ℝ} (hr : 0 ≤ r) (hrR : R < r) :
    p.compactAngularMean k R r = 0 := by
  unfold compactAngularMean
  have he : (fun θ : AngularSphere d =>
      (Metric.closedBall (0 : constrainedPlane d) R).indicator (p.realPoleFactor k)
        (r • θ.val)) = 0 := by
    funext θ
    have hθ : ‖θ.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    apply indicator_of_notMem
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hr,
      hθ, mul_one, not_le] using hrR
  rw [he]
  exact integral_zero _ _

theorem compactAngularMean_radial_measurable (k : ℕ) (hd : 0 < d)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKp : 0 ≤ Kp) (hKσ : 48 * Kp * σ ≤ 1)
    {R : ℝ} (hR : R < σ) :
    Measurable (fun x : ℝ => p.compactAngularMean k R (p.radialRadius x)) := by
  classical
  have := angularLaw_isProbability hd
  have hc := p.realPoleFactor_continuousOn k hσ hσ1 hKp hKσ hR
  have hm : Measurable ((Metric.closedBall (0 : constrainedPlane d) R).indicator
      (p.realPoleFactor k)) :=
    hc.measurable_piecewise continuousOn_const measurableSet_closedBall
  have hr : Continuous (fun z : ℝ × AngularSphere d => p.radialRadius z.1 • z.2.val) := by
    unfold radialRadius
    fun_prop
  exact ((hm.comp hr.measurable).stronglyMeasurable.integral_prod_right').measurable

theorem normalizedPoleError_measurable (k : ℕ) (hd : 0 < d)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKp : 0 ≤ Kp) (hKσ : 48 * Kp * σ ≤ 1)
    {R : ℝ} (hR : R < σ) : Measurable (p.normalizedPoleError k R) := by
  have hm := p.compactAngularMean_radial_measurable k hd hσ hσ1 hKp hKσ hR
  unfold normalizedPoleError
  apply measurable_const.mul (hm.sub ?_)
  unfold angularQuadraticPole radialRadius
  fun_prop

end
end IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
