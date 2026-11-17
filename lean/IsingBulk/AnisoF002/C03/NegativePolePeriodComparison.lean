import IsingBulk.AnisoF002.C03.NegativePhysicalRadialComparison
import IsingBulk.AnisoF002.C03.NegativeComplexQuadraticPeriod

/-!
# The complete compact physical pole compared with the full quadratic period

Both integrals use the actual independent-coordinate measure and the full
squared Vandermonde.  The error estimate includes the entire angular law,
the compact pole region and the omitted outer part of the quadratic
period.  All normalization constants are explicit.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section

theorem radialPower_particleExponent_odd {l : ℕ} (hl : 0 < l) :
    radialPower (2 * l) = 2 * (particleExponent (2 * l + 1) - 1) + 1 := by
  apply (radialPower_of_integer_shape ?_).2
  rw [particleExponent_odd, radialShape_even_dimension hl]

end
end IsingBulk.AnisoF002.NegativeHT.Angular

namespace IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
noncomputable section
open MeasureTheory Set Angular

variable {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {d : ℕ}
variable (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)

def compactPoleIntegral (k : ℕ) (R : ℝ) : ℂ :=
  ∫ v : constrainedPlane d,
    planeVandermonde v • (Metric.closedBall (0 : constrainedPlane d) R).indicator
      (p.realPoleFactor k) v ∂independentMeasure d

def fullQuadraticPeriod (_p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)
    (k : ℕ) : ℂ :=
  ∫ v : constrainedPlane d, planeVandermonde v •
    (1 / angularQuadraticPole d (windingTau (d + 1))
      (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
        (Real.cos φ) (Real.sin φ)) ‖v‖ ^ k) ∂independentMeasure d

def poleRadialScaleFactor : ℝ :=
  constrainedGaussianIntegral d / Real.Gamma (radialShape d) *
    p.radialScale ^ particleExponent (d + 1)

def positiveRadialNormalizer (k : ℕ) : ℝ :=
  p.poleRadialScaleFactor / windingTau (d + 1) ^ k * radialBeta (particleExponent (d + 1)) (k - 1)

theorem poleRadialScaleFactor_pos : 0 < p.poleRadialScaleFactor := by
  exact mul_pos (div_pos (constrainedGaussianIntegral_pos d)
    (Real.Gamma_pos_of_pos (radialShape_pos d))) (pow_pos p.radialScale_pos _)

theorem fullQuadraticPeriod_eq_actual (k : ℕ) :
    p.fullQuadraticPeriod k =
      ∫ v : constrainedPlane d, quadraticPeriodIntegrand d k (windingTau (d + 1))
        (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
          (Real.cos φ) (Real.sin φ) / (2 * ((d + 1 : ℕ) : ℂ))) v ∂independentMeasure d := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  have he : angularQuadraticPole d (windingTau (d + 1))
      (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
        (Real.cos φ) (Real.sin φ)) ‖v‖ =
      (windingTau (d + 1) : ℂ) +
        (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
          (Real.cos φ) (Real.sin φ) / (2 * ((d + 1 : ℕ) : ℂ))) * (‖v‖ ^ 2 : ℝ) := by
    unfold angularQuadraticPole
    push_cast
    ring
  simp only [quadraticPeriodIntegrand, he, Complex.real_smul, mul_one_div]

theorem compactPoleIntegral_scaled_identity (k : ℕ) (hd : 0 < d)
    (ha : radialPower d = 2 * (particleExponent (d + 1) - 1) + 1)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKp : 0 ≤ Kp) (hKσ : 48 * Kp * σ ≤ 1)
    {R : ℝ} (hR : R < σ) :
    p.compactPoleIntegral k R = p.poleRadialScaleFactor •
      ∫ x in Ioi (0 : ℝ), x ^ (particleExponent (d + 1) - 1) •
        p.compactAngularMean k R (p.radialRadius x) := by
  have hα : 0 < particleExponent (d + 1) := by
    have hsq : 4 ≤ (d + 1) ^ 2 := by nlinarith
    unfold particleExponent
    omega
  simpa only [compactPoleIntegral, poleRadialScaleFactor, compactAngularMean, radialRadius,
    Nat.sub_add_cancel hα] using p.compactPole_scaled_radial_identity k hd ha p.radialScale_pos
      hσ hσ1 hKp hKσ hR

theorem fullQuadraticPeriod_scaled_identity (k : ℕ) (hd : 0 < d)
    (ha : radialPower d = 2 * (particleExponent (d + 1) - 1) + 1) :
    p.fullQuadraticPeriod k = p.poleRadialScaleFactor •
      ∫ x in Ioi (0 : ℝ), x ^ (particleExponent (d + 1) - 1) •
        (1 / angularQuadraticPole d (windingTau (d + 1))
          (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
            (Real.cos φ) (Real.sin φ)) (p.radialRadius x) ^ k) := by
  have hα : 0 < particleExponent (d + 1) := by
    have hsq : 4 ≤ (d + 1) ^ 2 := by nlinarith
    unfold particleExponent
    omega
  let f : ℝ → ℂ := fun q => 1 / ((windingTau (d + 1) : ℂ) +
    firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ)) (Real.cos φ) (Real.sin φ) *
      ((q / (2 * ((d + 1 : ℕ) : ℝ)) : ℝ) : ℂ)) ^ k
  have hh := vandermonde_quadratic_complex_integral hd ha f
  rw [radial_power_scale (particleExponent (d + 1) - 1) p.radialScale_pos f,
    smul_smul, Nat.sub_add_cancel hα] at hh
  change p.fullQuadraticPeriod k = p.poleRadialScaleFactor •
    ∫ x in Ioi (0 : ℝ), x ^ (particleExponent (d + 1) - 1) • f (p.radialScale * x) at hh
  rw [hh]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only [f, angularQuadraticPole]
  rw [p.radialRadius_sq hx.le]

theorem pole_period_difference_identity {k : ℕ} (hd : 0 < d)
    (ha : radialPower d = 2 * (particleExponent (d + 1) - 1) + 1)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKp : 0 ≤ Kp) (hKσ : 48 * Kp * σ ≤ 1)
    {R : ℝ} (hR : R < σ)
    (hEi : IntegrableOn (fun x : ℝ => x ^ (particleExponent (d + 1) - 1) •
      p.normalizedPoleError k R x) (Ioi (0 : ℝ)))
    (hMi : IntegrableOn (fun x : ℝ => x ^ (particleExponent (d + 1) - 1) •
      p.normalizedQuadraticFactor k x) (Ioi (0 : ℝ))) :
    (windingTau (d + 1) : ℂ) ^ k * (p.compactPoleIntegral k R - p.fullQuadraticPeriod k) =
      p.poleRadialScaleFactor • ∫ x in Ioi (0 : ℝ), x ^ (particleExponent (d + 1) - 1) •
        p.normalizedPoleError k R x := by
  let A : ℝ → ℂ := fun x => x ^ (particleExponent (d + 1) - 1) •
    ((windingTau (d + 1) : ℂ) ^ k * p.compactAngularMean k R (p.radialRadius x))
  let M : ℝ → ℂ := fun x => x ^ (particleExponent (d + 1) - 1) • p.normalizedQuadraticFactor k x
  have hAE : A = (fun x => x ^ (particleExponent (d + 1) - 1) •
      p.normalizedPoleError k R x) + M := by
    funext x
    dsimp only [A, M, Pi.add_apply, normalizedPoleError, normalizedQuadraticFactor]
    simp only [Complex.real_smul]
    ring
  have hAi : IntegrableOn A (Ioi (0 : ℝ)) := by rw [hAE]; exact hEi.add hMi
  have hEM : (fun x => x ^ (particleExponent (d + 1) - 1) • p.normalizedPoleError k R x) =
      A - M := by rw [hAE, add_sub_cancel_right]
  have hI : (∫ x in Ioi (0 : ℝ), x ^ (particleExponent (d + 1) - 1) •
      p.normalizedPoleError k R x) =
      (∫ x in Ioi (0 : ℝ), A x) - ∫ x in Ioi (0 : ℝ), M x := by
    rw [hEM]
    exact integral_sub hAi hMi
  have hA : (∫ x in Ioi (0 : ℝ), A x) = (windingTau (d + 1) : ℂ) ^ k *
      ∫ x in Ioi (0 : ℝ), x ^ (particleExponent (d + 1) - 1) •
        p.compactAngularMean k R (p.radialRadius x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp only [A]
    simp only [Complex.real_smul]
    ring
  have hM : (∫ x in Ioi (0 : ℝ), M x) = (windingTau (d + 1) : ℂ) ^ k *
      ∫ x in Ioi (0 : ℝ), x ^ (particleExponent (d + 1) - 1) •
        (1 / angularQuadraticPole d (windingTau (d + 1))
          (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
            (Real.cos φ) (Real.sin φ)) (p.radialRadius x) ^ k) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp only [M, normalizedQuadraticFactor]
    simp only [Complex.real_smul]
    ring
  rw [p.compactPoleIntegral_scaled_identity k hd ha hσ hσ1 hKp hKσ hR,
    p.fullQuadraticPeriod_scaled_identity k hd ha, hI, hA, hM]
  simp only [Complex.real_smul]
  ring

set_option maxHeartbeats 1200000 in
theorem complete_physical_pole_period_comparison {k : ℕ} (hd : 2 ≤ d)
    (ha : radialPower d = 2 * (particleExponent (d + 1) - 1) + 1)
    (hk : 64 * (d + 1) ^ 2 ≤ k)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKρ : 0 ≤ Kρ) (hKp : 0 ≤ Kp)
    (hKσ : 768 * Kp * σ ≤ 1)
    (hupper : (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)).re ≤ 2)
    (hlarge : 64 * (Kρ * (1 + 2 * Real.pi ^ 2)) ≤ ((d + 1 : ℕ) : ℝ))
    {R δ : ℝ} (hR : 0 < R) (hRσ : R < σ)
    (hRcentral : 1024 * ((d + 1 : ℕ) : ℝ) / (k : ℝ) < R ^ 2)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hscale : δ ^ 2 = (((d + 1 : ℕ) : ℝ)) ^ 2 / (k : ℝ))
    (hsmall : 2 * (1024 : ℝ) ^ 2 * (Kρ + Kp) * δ ≤ 1 / 32) :
    ‖p.compactPoleIntegral k R - p.fullQuadraticPeriod k‖ ≤
      (angularPerturbationConstant * (2 * (1024 : ℝ) ^ 2 * (Kρ + Kp)) * δ +
        Real.exp (-(((d + 1 : ℕ) : ℝ)) ^ 2 / 4)) * p.positiveRadialNormalizer k := by
  obtain ⟨hEi, hEb⟩ := p.complete_beta_radial_error hd hk hσ hσ1 hKρ hKp hKσ hupper hlarge
    hR hRσ hRcentral hδ hδ1 hscale hsmall
  have hNsq : 4 ≤ (d + 1) ^ 2 := by nlinarith
  have hαk : particleExponent (d + 1) < k := by
    have hh := particleExponent_le_sq (d + 1)
    omega
  have hKweak : 48 * Kp * σ ≤ 1 := by nlinarith
  have hMi := p.weighted_normalizedQuadraticFactor_integrable (by omega) hαk
  have hId := p.pole_period_difference_identity (by omega) ha hσ hσ1 hKp hKweak hRσ hEi hMi
  have hnorm := congrArg norm hId
  have ht := windingTau_pos (d + 1) (by omega)
  have hs := p.poleRadialScaleFactor_pos
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le,
    norm_smul, Real.norm_of_nonneg hs.le] at hnorm
  have hb := mul_le_mul_of_nonneg_left hEb hs.le
  rw [← hnorm] at hb
  calc
    _ ≤ (p.poleRadialScaleFactor *
        ((angularPerturbationConstant * (2 * (1024 : ℝ) ^ 2 * (Kρ + Kp)) * δ +
          Real.exp (-(((d + 1 : ℕ) : ℝ)) ^ 2 / 4)) *
            radialBeta (particleExponent (d + 1)) (k - 1))) / windingTau (d + 1) ^ k := by
      apply (le_div_iff₀ (pow_pos ht k)).mpr
      convert hb using 1; ring
    _ = _ := by unfold positiveRadialNormalizer; ring

end
end IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
