import IsingBulk.AnisoF002.C03.NegativeFullPolarIntegral
import IsingBulk.AnisoF002.C03.NegativePhysicalTailAbsorption

/-!
# Genuine compact first-winding pole integrals

The physical pole is nonzero on the real constrained ball.  Its complete
factor is continuous on every smaller closed ball, so the polar Fubini
identity applies with proved integrability, not an integration premise.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem complexPlaneEmbedding_complex_square {d : ℕ} (v : constrainedPlane d) :
    (∑ i, (complexPlaneEmbedding v : Fin (d + 1) → ℂ) i ^ 2) = (‖v‖ ^ 2 : ℝ) := by
  rw [constrained_norm_sq]
  unfold complexPlaneEmbedding
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_sum]

theorem gaussianLaw_integrable_polar_complex {d : ℕ} (hd : 0 < d)
    (f : constrainedPlane d → ℂ) (hi : Integrable f (gaussianLaw d)) :
    Integrable (fun z : AngularSphere d × Ioi (0 : ℝ) => f (z.2.val • z.1.val))
      ((angularLaw d).prod (radialLaw d)) := by
  let e := homeomorphUnitSphereProd (constrainedPlane d)
  have hi' : Integrable (fun v : ({0}ᶜ : Set (constrainedPlane d)) => f v.val)
      ((gaussianLaw d).comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hi.integrableOn
  apply ((gaussianLaw_polar_measurePreserving hd).integrable_comp_emb e.measurableEmbedding).mp
  apply hi'.congr
  apply Filter.Eventually.of_forall
  intro v
  exact (congrArg f (congrArg Subtype.val (e.symm_apply_apply v))).symm

theorem compact_polar_lift_integrable {d : ℕ} (hd : 0 < d) (R : ℝ)
    (f : constrainedPlane d → ℂ) (hf : ContinuousOn f (Metric.closedBall 0 R)) :
    Integrable (fun z : AngularSphere d × Ioi (0 : ℝ) =>
      Real.exp (z.2.val ^ 2) • (Metric.closedBall (0 : constrainedPlane d) R).indicator f
        (z.2.val • z.1.val)) ((angularLaw d).prod (radialLaw d)) := by
  have := gaussianLaw_isProbability hd
  have hc : ContinuousOn (fun v : constrainedPlane d => Real.exp (‖v‖ ^ 2) • f v)
      (Metric.closedBall 0 R) :=
    (Real.continuous_exp.comp (continuous_norm.pow 2)).continuousOn.smul hf
  have hi := (hc.integrableOn_compact (isCompact_closedBall (0 : constrainedPlane d) R)
    (μ := gaussianLaw d)).integrable_indicator measurableSet_closedBall
  have he : (Metric.closedBall (0 : constrainedPlane d) R).indicator
      (fun v => Real.exp (‖v‖ ^ 2) • f v) =
        (fun v => Real.exp (‖v‖ ^ 2) • (Metric.closedBall (0 : constrainedPlane d) R).indicator f v) := by
    funext v
    by_cases hv : v ∈ Metric.closedBall (0 : constrainedPlane d) R <;> simp [hv]
  rw [he] at hi
  have hp := gaussianLaw_integrable_polar_complex hd _ hi
  convert hp using 1
  funext z
  have hθ : ‖z.1.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.1.property
  rw [norm_smul, Real.norm_of_nonneg z.2.property.le, hθ, mul_one]

end
end IsingBulk.AnisoF002.NegativeHT.Angular

namespace IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
noncomputable section
open MeasureTheory Set Angular
open scoped BigOperators

def realPoleFactor {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {d : ℕ}
    (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)
    (k : ℕ) (v : constrainedPlane d) : ℂ :=
  Complex.exp (p.densityLog (complexPlaneEmbedding v)) / p.pole (complexPlaneEmbedding v) ^ k

theorem realPole_ne_zero {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {d : ℕ}
    (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKp : 0 ≤ Kp) (hKσ : 48 * Kp * σ ≤ 1)
    (v : constrainedPlane d) (hv : ‖v‖ < σ) : p.pole (complexPlaneEmbedding v) ≠ 0 := by
  have hQ : displacementSquare (d + 1) (complexPlaneEmbedding v) < σ ^ 2 := by
    rw [complexPlaneEmbedding_square]
    nlinarith [norm_nonneg v]
  have he := higher_pole_error_small (d + 1) (by omega) (complexPlaneEmbedding v)
    hKp hσ hσ1 hKσ hQ (p.pole_error _ hQ)
  rw [complexPlaneEmbedding_square, complexPlaneEmbedding_complex_square] at he
  have hmodel : (windingTau (d + 1) : ℂ) +
      firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ)) (Real.cos φ) (Real.sin φ) *
        (‖v‖ ^ 2 : ℝ) / (2 * ((d + 1 : ℕ) : ℂ)) =
      (windingTau (d + 1) : ℂ) +
      firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ)) (Real.cos φ) (Real.sin φ) *
        ((‖v‖ ^ 2 / (2 * ((d + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by push_cast; ring
  rw [hmodel] at he
  exact (actual_pole_quarter_control (by positivity : 0 < ((d + 1 : ℕ) : ℝ))
    (windingTau_pos (d + 1) (by omega)) (sq_nonneg ‖v‖) p.curvature_re he).2.2.2

theorem realPoleFactor_continuousOn {b B : ℂ → ℂ} {φ σ C Kρ Kp R : ℝ} {d : ℕ}
    (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp) (k : ℕ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKp : 0 ≤ Kp) (hKσ : 48 * Kp * σ ≤ 1)
    (hR : R < σ) : ContinuousOn (p.realPoleFactor k) (Metric.closedBall 0 R) := by
  intro v hv
  have hnorm : ‖v‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hv' : ‖v‖ < σ := hnorm.trans_lt hR
  have hQ : displacementSquare (d + 1) (complexPlaneEmbedding v) < σ ^ 2 := by
    rw [complexPlaneEmbedding_square]
    nlinarith [norm_nonneg v]
  have hTa := p.pole_analytic (complexPlaneEmbedding v)
    (zeroSumDisplacements_mem_ball_of_square_lt _ hσ hQ)
  have hla := p.log_analytic (complexPlaneEmbedding v) hQ
  exact ((Complex.continuous_exp.continuousAt.comp
    (hla.continuousAt.comp (continuous_complexPlaneEmbedding d).continuousAt)).div
      ((hTa.continuousAt.comp (continuous_complexPlaneEmbedding d).continuousAt).pow k)
      (pow_ne_zero _ (p.realPole_ne_zero hσ hσ1 hKp hKσ v hv'))).continuousWithinAt

theorem compactPole_full_polar_identity {b B : ℂ → ℂ} {φ σ C Kρ Kp R : ℝ} {d : ℕ}
    (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp) (k : ℕ) (hd : 0 < d)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKp : 0 ≤ Kp) (hKσ : 48 * Kp * σ ≤ 1)
    (hR : R < σ) :
    (∫ v : constrainedPlane d,
      planeVandermonde v • (Metric.closedBall (0 : constrainedPlane d) R).indicator
        (p.realPoleFactor k) v ∂independentMeasure d) =
      (2 * constrainedGaussianIntegral d / Real.Gamma (radialShape d)) •
        ∫ r in Ioi (0 : ℝ), r ^ radialPower d •
          (∫ θ : AngularSphere d,
            (Metric.closedBall (0 : constrainedPlane d) R).indicator (p.realPoleFactor k)
              (r • θ.val) ∂angularLaw d) := by
  apply vandermonde_full_polar_integral hd
  exact compact_polar_lift_integrable hd R (p.realPoleFactor k)
    (p.realPoleFactor_continuousOn k hσ hσ1 hKp hKσ hR)

end
end IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
