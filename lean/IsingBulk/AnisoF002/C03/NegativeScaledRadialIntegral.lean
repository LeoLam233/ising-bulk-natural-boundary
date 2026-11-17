import IsingBulk.AnisoF002.C03.NegativePoleIntegral

/-!
# Exact scaled radial coordinates for the complete physical pole integral

The entire angular measure is retained.  The substitution is applied to
the genuine compact pole integral, with its independently proved
integrability and exact independent-coordinate Vandermonde normalization.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set

theorem radial_sqrt_substitution (a : ℕ) (f : ℝ → ℂ) :
    (∫ r in Ioi (0 : ℝ), r ^ (2 * a + 1) • f r) =
      (1 / 2 : ℝ) • ∫ q in Ioi (0 : ℝ), q ^ a • f (Real.sqrt q) := by
  calc
    _ = ∫ r in Ioi (0 : ℝ), r ^ (2 * a + 1) • f (Real.sqrt (r ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [Real.sqrt_sq (show 0 ≤ r from hr.le)]
    _ = _ := radial_square_substitution a (fun q => f (Real.sqrt q))

theorem radial_power_scale (a : ℕ) {c : ℝ} (hc : 0 < c) (f : ℝ → ℂ) :
    (∫ q in Ioi (0 : ℝ), q ^ a • f q) =
      c ^ (a + 1) • ∫ x in Ioi (0 : ℝ), x ^ a • f (c * x) := by
  have he := integral_comp_mul_left_Ioi' (fun q : ℝ => q ^ a • f q) 0 hc
  simp only [mul_zero] at he
  rw [← he]
  simp_rw [mul_pow, mul_smul]
  rw [integral_smul, smul_smul, pow_succ]
  congr 1
  ring

theorem radial_scaled_sqrt_substitution (a : ℕ) {c : ℝ} (hc : 0 < c)
    (f : ℝ → ℂ) :
    (∫ r in Ioi (0 : ℝ), r ^ (2 * a + 1) • f r) =
      (c ^ (a + 1) / 2) •
        ∫ x in Ioi (0 : ℝ), x ^ a • f (Real.sqrt (c * x)) := by
  rw [radial_sqrt_substitution,
    radial_power_scale a hc (fun q => f (Real.sqrt q)), smul_smul]
  congr 1
  ring

theorem vandermonde_full_scaled_radial_integral {d a : ℕ} (hd : 0 < d)
    (ha : radialPower d = 2 * a + 1) {c : ℝ} (hc : 0 < c)
    (f : constrainedPlane d → ℂ)
    (hi : Integrable (fun z : AngularSphere d × Ioi (0 : ℝ) =>
      Real.exp (z.2.val ^ 2) • f (z.2.val • z.1.val))
        ((angularLaw d).prod (radialLaw d))) :
    (∫ v : constrainedPlane d, planeVandermonde v • f v ∂independentMeasure d) =
      (constrainedGaussianIntegral d / Real.Gamma (radialShape d) * c ^ (a + 1)) •
        ∫ x in Ioi (0 : ℝ), x ^ a •
          (∫ θ : AngularSphere d, f (Real.sqrt (c * x) • θ.val) ∂angularLaw d) := by
  rw [vandermonde_full_polar_integral hd f hi, ha,
    radial_scaled_sqrt_substitution a hc, smul_smul]
  congr 1
  ring

end
end IsingBulk.AnisoF002.NegativeHT.Angular

namespace IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
noncomputable section
open MeasureTheory Set Angular

theorem compactPole_scaled_radial_identity
    {b B : ℂ → ℂ} {φ σ C Kρ Kp R c : ℝ} {d a : ℕ}
    (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp) (k : ℕ) (hd : 0 < d)
    (ha : radialPower d = 2 * a + 1) (hc : 0 < c)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKp : 0 ≤ Kp) (hKσ : 48 * Kp * σ ≤ 1)
    (hR : R < σ) :
    (∫ v : constrainedPlane d,
      planeVandermonde v • (Metric.closedBall (0 : constrainedPlane d) R).indicator
        (p.realPoleFactor k) v ∂independentMeasure d) =
      (constrainedGaussianIntegral d / Real.Gamma (radialShape d) * c ^ (a + 1)) •
        ∫ x in Ioi (0 : ℝ), x ^ a •
          (∫ θ : AngularSphere d,
            (Metric.closedBall (0 : constrainedPlane d) R).indicator (p.realPoleFactor k)
              (Real.sqrt (c * x) • θ.val) ∂angularLaw d) := by
  apply vandermonde_full_scaled_radial_integral hd ha hc
  exact compact_polar_lift_integrable hd R (p.realPoleFactor k)
    (p.realPoleFactor_continuousOn k hσ hσ1 hKp hKσ hR)

end
end IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
