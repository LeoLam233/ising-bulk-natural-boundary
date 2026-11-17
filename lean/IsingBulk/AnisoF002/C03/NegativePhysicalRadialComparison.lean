import IsingBulk.AnisoF002.C03.NegativeNormalizedPoleBounds
import IsingBulk.AnisoF002.C03.NegativeIntegratedBetaError

/-!
# Integrated whole-radius error of the complete physical first-winding pole

The central and tail hypotheses are discharged by the constructed
physical pole and density.  The actual entire angular mean, the fixed
compact pole ball, every positive radial coordinate and every sufficiently
large integer order occur in the conclusion.
-/

namespace IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
noncomputable section
open MeasureTheory Set Angular

variable {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {d : ℕ}
variable (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)

theorem complete_beta_radial_error {k : ℕ} (hd : 2 ≤ d)
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
    IntegrableOn (fun x : ℝ => x ^ (particleExponent (d + 1) - 1) •
      p.normalizedPoleError k R x) (Ioi (0 : ℝ)) ∧
    ‖∫ x in Ioi (0 : ℝ), x ^ (particleExponent (d + 1) - 1) •
      p.normalizedPoleError k R x‖ ≤
      (angularPerturbationConstant * (2 * (1024 : ℝ) ^ 2 * (Kρ + Kp)) * δ +
        Real.exp (-(((d + 1 : ℕ) : ℝ)) ^ 2 / 4)) *
          radialBeta (particleExponent (d + 1)) (k - 1) := by
  have hNsq : 4 ≤ (d + 1) ^ 2 := by nlinarith
  have hk0 : 0 < k := by omega
  have hk8 : 8 ≤ k := by omega
  have hkN : (((d + 1 : ℕ) : ℝ)) ^ 2 ≤ (k : ℝ) := by
    exact_mod_cast (show (d + 1) ^ 2 ≤ k by omega)
  have hKweak : 48 * Kp * σ ≤ 1 := by nlinarith
  have hpc := angularPerturbationConstant_pos
  apply integrated_full_beta_error (d + 1) k (by omega) hk
    (by positivity)
    (p.normalizedPoleError_measurable k (by omega) hσ hσ1 hKp hKweak hRσ).aestronglyMeasurable
  · intro x hx hcut
    exact p.normalizedPoleError_central hd hk0 hσ hσ1 hKρ hKp hKweak hupper
      hR hRσ hRcentral hδ hδ1 hscale hsmall hx hcut
  · intro x hcut
    exact p.normalizedPoleError_tail (by omega) hk8 hσ hσ1 hKρ hKp hKσ hupper hlarge hkN hRσ hcut

def normalizedQuadraticFactor (k : ℕ) (x : ℝ) : ℂ :=
  (windingTau (d + 1) : ℂ) ^ k *
    (1 / angularQuadraticPole d (windingTau (d + 1))
      (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
        (Real.cos φ) (Real.sin φ)) (p.radialRadius x) ^ k)

theorem normalizedQuadraticFactor_measurable (k : ℕ) : Measurable (p.normalizedQuadraticFactor k) := by
  unfold normalizedQuadraticFactor angularQuadraticPole radialRadius
  fun_prop

theorem weighted_normalizedQuadraticFactor_integrable {k : ℕ}
    (hd : 0 < d) (hk : particleExponent (d + 1) < k) :
    IntegrableOn (fun x : ℝ => x ^ (particleExponent (d + 1) - 1) •
      p.normalizedQuadraticFactor k x) (Ioi (0 : ℝ)) := by
  have hα0 : 0 < particleExponent (d + 1) := by
    have hsq : 4 ≤ (d + 1) ^ 2 := by nlinarith
    unfold particleExponent
    omega
  have hk1 : 1 ≤ k := by omega
  have hi := integrableOn_radialBetaDensity (particleExponent (d + 1)) (k - 1) hα0 (by omega)
  apply hi.mono' ((continuous_id.pow _).aestronglyMeasurable.smul
    (p.normalizedQuadraticFactor_measurable k).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change ‖x ^ (particleExponent (d + 1) - 1) • p.normalizedQuadraticFactor k x‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hx.le _)]
  have hh := mul_le_mul_of_nonneg_left (p.normalized_quadratic_bound k hx.le)
    (pow_nonneg hx.le (particleExponent (d + 1) - 1))
  simpa only [normalizedQuadraticFactor, radialBetaDensity, Nat.sub_add_cancel hk1,
    div_eq_mul_inv, one_mul, mul_assoc] using hh

end
end IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
