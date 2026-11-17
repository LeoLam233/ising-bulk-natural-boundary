import IsingBulk.AnisoF002.C03.NegativePoleIntegral
import IsingBulk.AnisoF002.C03.NegativeArbitraryOrderTail

/-!
# Central and outer means of the actual complete physical pole

These are bounds on the entire angular mean of the constructed pole
and complete logarithmic density.  They retain its complex phase and
use the actual angular probability measure in every direction.
-/

namespace IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
noncomputable section
open MeasureTheory Set Angular

def angularPoleMean {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {d : ℕ}
    (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)
    (k : ℕ) (r : ℝ) : ℂ :=
  ∫ θ : AngularSphere d, p.realPoleFactor k (r • θ.val) ∂angularLaw d

theorem angularPoleFactor_continuous {b B : ℂ → ℂ} {φ σ C Kρ Kp r : ℝ} {d : ℕ}
    (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp) (k : ℕ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKp : 0 ≤ Kp) (hKσ : 48 * Kp * σ ≤ 1)
    (hr : 0 ≤ r) (hrσ : r < σ) :
    Continuous (fun θ : AngularSphere d => p.realPoleFactor k (r • θ.val)) := by
  have hc : Continuous (fun θ : AngularSphere d => r • θ.val) :=
    (continuous_subtype_val : Continuous (fun θ : AngularSphere d => (θ.val : constrainedPlane d))).const_smul r
  apply (p.realPoleFactor_continuousOn k hσ hσ1 hKp hKσ hrσ).comp_continuous hc
  intro θ
  have hθ : ‖θ.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hr, hθ, mul_one]
  exact le_rfl

theorem angularPoleFactor_integrable {b B : ℂ → ℂ} {φ σ C Kρ Kp r : ℝ} {d : ℕ}
    (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp) (k : ℕ) (hd : 0 < d)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKp : 0 ≤ Kp) (hKσ : 48 * Kp * σ ≤ 1)
    (hr : 0 ≤ r) (hrσ : r < σ) :
    Integrable (fun θ : AngularSphere d => p.realPoleFactor k (r • θ.val)) (angularLaw d) := by
  have := angularLaw_isProbability hd
  exact (p.angularPoleFactor_continuous k hσ hσ1 hKp hKσ hr hrσ).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

theorem angularPoleMean_sub_constant {b B : ℂ → ℂ} {φ σ C Kρ Kp r : ℝ} {d : ℕ}
    (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp) (k : ℕ) (hd : 0 < d)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKp : 0 ≤ Kp) (hKσ : 48 * Kp * σ ≤ 1)
    (hr : 0 ≤ r) (hrσ : r < σ) (z : ℂ) :
    (∫ θ : AngularSphere d, (p.realPoleFactor k (r • θ.val) - z) ∂angularLaw d) =
      p.angularPoleMean k r - z := by
  have := angularLaw_isProbability hd
  rw [integral_sub (p.angularPoleFactor_integrable k hd hσ hσ1 hKp hKσ hr hrσ)
    (integrable_const z)]
  simp only [angularPoleMean, integral_const, probReal_univ, one_smul]

theorem central_angularPoleMean_comparison
    {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {d k : ℕ}
    (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)
    (hd : 2 ≤ d) (hk : 0 < k) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hKρ : 0 ≤ Kρ) (hKp : 0 ≤ Kp) (hKσ : 48 * Kp * σ ≤ 1)
    {r A δ : ℝ} (hr : 0 ≤ r) (hrσ : r < σ) (hA : 1 ≤ A)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hscale : δ ^ 2 = (((d + 1 : ℕ) : ℝ)) ^ 2 / (k : ℝ))
    (hcentral : r ^ 2 ≤ A * ((d + 1 : ℕ) : ℝ) / (k : ℝ))
    (hsmall : 2 * A ^ 2 * (Kρ + Kp) * δ ≤ 1 / 32) :
    let h := firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)
    let D := windingTau (d + 1) + h.re * r ^ 2 / (2 * ((d + 1 : ℕ) : ℝ))
    ‖p.angularPoleMean k r - 1 / angularQuadraticPole d (windingTau (d + 1)) h r ^ k‖ ≤
      angularPerturbationConstant * (2 * A ^ 2 * (Kρ + Kp)) * δ / D ^ k := by
  dsimp only
  have hh := (p.complete_central_angular_comparison hd hk hσ hσ1 hKρ hKp hKσ
    hr hrσ hA hδ hδ1 hscale hcentral hsmall).2
  rw [← p.angularPoleMean_sub_constant k (by omega) hσ hσ1 hKp hKσ hr hrσ]
  simpa only [realPoleFactor, complexPlaneEmbedding_smul_angular] using hh

set_option maxHeartbeats 1500000 in
theorem outer_angularPoleMean_comparison
    {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {d k : ℕ}
    (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)
    (hd : 0 < d) (hk8 : 8 ≤ k)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKρ : 0 ≤ Kρ) (hKp : 0 ≤ Kp)
    (hKσ : 768 * Kp * σ ≤ 1)
    (hupper : (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)).re ≤ 2)
    (hlarge : 64 * (Kρ * (1 + 2 * Real.pi ^ 2)) ≤ ((d + 1 : ℕ) : ℝ))
    (hk : (((d + 1 : ℕ) : ℝ)) ^ 2 ≤ (k : ℝ))
    {r A : ℝ} (hr : 0 ≤ r) (hrσ : r < σ) (hA : 2 * Real.pi ^ 2 ≤ A)
    (houter : A * ((d + 1 : ℕ) : ℝ) / (k : ℝ) ≤ r ^ 2) :
    let h := firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)
    let x := h.re * r ^ 2 / (2 * ((d + 1 : ℕ) : ℝ) * windingTau (d + 1))
    ‖p.angularPoleMean k r - 1 / angularQuadraticPole d (windingTau (d + 1)) h r ^ k‖ ≤
      1 / (windingTau (d + 1) ^ k * (1 + x) ^ (k / 2 + k / 4 + 1)) := by
  dsimp only
  let h := firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
    (Real.cos φ) (Real.sin φ)
  let τ := windingTau (d + 1)
  let D := τ + h.re * r ^ 2 / (2 * ((d + 1 : ℕ) : ℝ))
  let x := h.re * r ^ 2 / (2 * ((d + 1 : ℕ) : ℝ) * τ)
  have hτ : 0 < τ := windingTau_pos (d + 1) (by omega)
  have hre : (1 / 2 : ℝ) ≤ h.re := p.curvature_re
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hDeq : D = τ * (1 + x) := by dsimp [D, x]; field_simp
  have hKweak : 48 * Kp * σ ≤ 1 := by nlinarith
  have hQ (θ : AngularSphere d) :
      displacementSquare (d + 1) (angularComplexDisplacement r θ) < σ ^ 2 := by
    rw [angularComplexDisplacement_square]
    nlinarith
  have he := p.complete_outer_angular_absorption hσ hσ1 hKρ hKp hKσ hupper hlarge hk
    hr hrσ hA houter
  have := angularLaw_isProbability hd
  rw [← p.angularPoleMean_sub_constant k hd hσ hσ1 hKp hKweak hr hrσ]
  have hpoint (θ : AngularSphere d) :
      ‖p.realPoleFactor k (r • θ.val) - 1 / angularQuadraticPole d τ h r ^ k‖ ≤
        1 / (τ ^ k * (1 + x) ^ (k / 2 + k / 4 + 1)) := by
    have hsmall := higher_pole_error_small (d + 1) (by omega) (angularComplexDisplacement r θ)
      hKp hσ hσ1 hKweak (hQ θ) (p.pole_error _ (hQ θ))
    rw [angular_quadratic_identity, angularComplexDisplacement_square] at hsmall
    have hquarter := actual_pole_quarter_control
      (by positivity : 0 < ((d + 1 : ℕ) : ℝ)) hτ (sq_nonneg r) hre hsmall
    let E := ‖p.densityLog (angularComplexDisplacement r θ)‖ +
      2 * (k : ℝ) * ‖p.pole (angularComplexDisplacement r θ) -
        angularQuadraticPole d τ h r‖ / D
    have hEb : E ≤ (k : ℝ) / 8 * Real.log (1 + x) := he θ
    have herror := complete_pole_integrand_error k (p.densityLog (angularComplexDisplacement r θ))
      (p.pole (angularComplexDisplacement r θ)) (angularQuadraticPole d τ h r) D
      hD hquarter.2.1 hquarter.1
    simp only [realPoleFactor, complexPlaneEmbedding_smul_angular]
    calc
      _ ≤ (Real.exp E - 1) / D ^ k := herror
      _ ≤ Real.exp E / D ^ k := div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = (Real.exp E / (1 + x) ^ k) / τ ^ k := by rw [hDeq, mul_pow]; ring
      _ ≤ (1 / (1 + x) ^ (k / 2 + k / 4 + 1)) / τ ^ k :=
        div_le_div_of_nonneg_right (absorbed_exponential_majorant hk8 hx hEb) (by positivity)
      _ = _ := by rw [div_div, mul_comm ((1 + x) ^ (k / 2 + k / 4 + 1)) (τ ^ k)]
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := angularLaw d) (Filter.Eventually.of_forall hpoint)

end
end IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
