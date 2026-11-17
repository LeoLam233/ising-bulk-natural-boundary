import IsingBulk.AnisoF002.C03.NegativeRelativePoleError
import IsingBulk.AnisoF002.C03.NegativeCenterPeriod

/-!
# The integral of the literal physical residue

The residue here retains every one-body and pair factor, its temperature
derivative, and the physical square-root and independent-angle constants.
Its integral is identified with the compact pole integral already bounded
on the full real constrained cycle.  Integrability is proved on the actual
compact region, including all partial and total angular collisions.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open scoped BigOperators

theorem complexPlaneEmbedding_vandermonde {d : ℕ} (v : constrainedPlane d) :
    complexVandermondeSquared (d + 1) (complexPlaneEmbedding v) =
      (planeVandermonde v : ℂ) := by
  unfold complexVandermondeSquared planeVandermonde RegularTail.vandermondeSquared
    complexPlaneEmbedding
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_pow, ← Complex.ofReal_prod]

end
end IsingBulk.AnisoF002.NegativeHT.Angular

namespace IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
noncomputable section
open MeasureTheory Set Angular

variable {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {d : ℕ}
variable (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)

def physicalCenterDensity (_p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp) : ℂ :=
  filledNegativeDensityAt (d + 1) b (negativeGlobalPhase B φ)
    ((Real.pi / ((d + 1 : ℕ) : ℝ) : ℝ) : ℂ) (windingTau (d + 1) : ℂ) 0

def physicalResidueIntegrand (k : ℕ) (v : constrainedPlane d) : ℂ :=
  -(2 * completeNegativeNumerator (d + 1) b (negativeGlobalPhase B φ)
      ((Real.pi / ((d + 1 : ℕ) : ℝ) : ℝ) : ℂ) (p.pole (complexPlaneEmbedding v))
      (complexPlaneEmbedding v)) /
    phaseTemperatureSum (d + 1) (negativeGlobalPhase B φ)
      ((Real.pi / ((d + 1 : ℕ) : ℝ) : ℝ) : ℂ) (p.pole (complexPlaneEmbedding v))
      (complexPlaneEmbedding v) / p.pole (complexPlaneEmbedding v) ^ k

def physicalResidueIntegral (k : ℕ) (R : ℝ) : ℂ :=
  ∫ v in Metric.closedBall (0 : constrainedPlane d) R,
    p.physicalResidueIntegrand k v ∂independentMeasure d

theorem physicalResidueIntegrand_identity (k : ℕ) (hσ : 0 < σ)
    (v : constrainedPlane d) (hv : ‖v‖ < σ) :
    p.physicalResidueIntegrand k v =
      p.physicalCenterDensity * (planeVandermonde v : ℂ) * p.realPoleFactor k v := by
  have hQ : displacementSquare (d + 1) (complexPlaneEmbedding v) < σ ^ 2 := by
    rw [complexPlaneEmbedding_square]
    nlinarith [norm_nonneg v]
  unfold physicalResidueIntegrand
  rw [p.density_identity _ hQ, complexPlaneEmbedding_vandermonde]
  unfold physicalCenterDensity realPoleFactor
  ring

theorem physicalResidueIntegrand_integrableOn (k : ℕ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKp : 0 ≤ Kp) (hKσ : 48 * Kp * σ ≤ 1)
    {R : ℝ} (hR : R < σ) :
    IntegrableOn (p.physicalResidueIntegrand k) (Metric.closedBall 0 R)
      (independentMeasure d) := by
  have hc : ContinuousOn (fun v : constrainedPlane d =>
      p.physicalCenterDensity * (planeVandermonde v : ℂ) * p.realPoleFactor k v)
      (Metric.closedBall 0 R) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_planeVandermonde d))).continuousOn.mul
        (p.realPoleFactor_continuousOn k hσ hσ1 hKp hKσ hR)
  have he : EqOn (p.physicalResidueIntegrand k)
      (fun v => p.physicalCenterDensity * (planeVandermonde v : ℂ) * p.realPoleFactor k v)
      (Metric.closedBall 0 R) := by
    intro v hv
    apply p.physicalResidueIntegrand_identity k hσ v
    have hv' : ‖v‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    exact hv'.trans_lt hR
  exact (hc.congr he).integrableOn_compact (isCompact_closedBall _ _)

theorem physicalResidueIntegral_identity (k : ℕ) (hσ : 0 < σ)
    {R : ℝ} (hR : R < σ) :
    p.physicalResidueIntegral k R = p.physicalCenterDensity * p.compactPoleIntegral k R := by
  unfold physicalResidueIntegral compactPoleIntegral
  rw [← integral_indicator measurableSet_closedBall, ← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  by_cases hv : v ∈ Metric.closedBall (0 : constrainedPlane d) R
  · have hv' : ‖v‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    rw [indicator_of_mem hv, indicator_of_mem hv, p.physicalResidueIntegrand_identity k hσ v
      (hv'.trans_lt hR)]
    rw [Complex.real_smul]
    ring
  · simp only [indicator_of_notMem hv, smul_zero, mul_zero]

theorem physicalResidueIntegral_nonzero_center : p.physicalCenterDensity ≠ 0 :=
  p.center_density_ne_zero

theorem physicalResidueIntegral_relative_error {k : ℕ} {R ε : ℝ}
    (hσ : 0 < σ) (hR : R < σ)
    (he : ‖p.compactPoleIntegral k R - p.fullQuadraticPeriod k‖ ≤
      ε * ‖p.fullQuadraticPeriod k‖) :
    ‖p.physicalResidueIntegral k R - p.physicalCenterDensity * p.fullQuadraticPeriod k‖ ≤
      ε * ‖p.physicalCenterDensity * p.fullQuadraticPeriod k‖ := by
  rw [p.physicalResidueIntegral_identity k hσ hR, ← mul_sub, norm_mul, norm_mul]
  calc
    _ ≤ ‖p.physicalCenterDensity‖ * (ε * ‖p.fullQuadraticPeriod k‖) :=
      mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ = _ := by ring

end
end IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
