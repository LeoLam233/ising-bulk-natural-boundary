import IsingBulk.AnisoF002.C03.NegativePhysicalAngularError
import IsingBulk.AnisoF002.C03.NegativeRadialGeometry

/-!
# Complete physical outer-region absorption on one fixed real-cycle ball

The smaller radius and all constants are chosen before the particle
number.  Every angular direction is retained.  The pole and logarithm
are the constructed complete physical residue, not a substitute model.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

theorem tendsto_firstWindingCurvature_one (B : ℂ → ℂ) (hB : ContinuousAt B 0)
    (b s : ℝ) :
    Tendsto (fun n : ℕ => firstWindingCurvature n (B (windingTau n : ℂ)) b s)
      atTop (𝓝 1) := by
  have hd : Tendsto (fun n : ℕ => Real.pi / (n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat Real.pi
  have hcR : Tendsto (fun n : ℕ => Real.cos (Real.pi / (n : ℝ))) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Real.cos_zero] using
      Real.continuous_cos.continuousAt.tendsto.comp hd
  have hsR : Tendsto (fun n : ℕ => Real.sin (Real.pi / (n : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sin_zero] using
      Real.continuous_sin.continuousAt.tendsto.comp hd
  have hc : Tendsto (fun n : ℕ => (Real.cos (Real.pi / (n : ℝ)) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hcR
  have hs : Tendsto (fun n : ℕ => (Real.sin (Real.pi / (n : ℝ)) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hsR
  simpa only [firstWindingCurvature, zero_pow two_ne_zero, mul_zero, sub_zero] using
    hc.sub ((((tendsto_anisotropy_at_centers B hB).mul_const (b : ℂ)).div_const
      ((s : ℂ) ^ 2)).mul (hs.pow 2))

namespace PhysicalFirstWindingData

def restrictRadius {b B : ℂ → ℂ} {φ σ σ' C Kρ Kp : ℝ} {n : ℕ}
    (p : PhysicalFirstWindingData b B φ n σ C Kρ Kp)
    (hσ' : 0 < σ') (hσ : σ' ≤ σ) : PhysicalFirstWindingData b B φ n σ' C Kρ Kp := by
  have hQ (v : zeroSumDisplacements n) (hv : displacementSquare n v < σ' ^ 2) :
      displacementSquare n v < σ ^ 2 := hv.trans_le (by nlinarith)
  exact {
    pole := p.pole
    densityLog := p.densityLog
    pole_analytic := p.pole_analytic.mono (Metric.ball_subset_ball hσ)
    pole_center := p.pole_center
    phase := fun v hv => p.phase v (hQ v hv)
    pole_coarse := fun v hv => p.pole_coarse v (hQ v hv)
    phase_deriv_ne_zero := fun v hv => p.phase_deriv_ne_zero v (hQ v hv)
    log_analytic := fun v hv => p.log_analytic v (hQ v hv)
    center_density_ne_zero := p.center_density_ne_zero
    density_identity := fun v hv => p.density_identity v (hQ v hv)
    log_bound := fun v hv => p.log_bound v (hQ v hv)
    pole_error := fun v hv => p.pole_error v (hQ v hv)
    curvature_re := p.curvature_re }

open Angular

theorem complete_outer_angular_absorption
    {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {d k : ℕ}
    (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)
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
    let D := windingTau (d + 1) + h.re * r ^ 2 / (2 * ((d + 1 : ℕ) : ℝ))
    let x := h.re * r ^ 2 / (2 * ((d + 1 : ℕ) : ℝ) * windingTau (d + 1))
    ∀ θ : AngularSphere d,
      ‖p.densityLog (angularComplexDisplacement r θ)‖ +
        2 * (k : ℝ) * ‖p.pole (angularComplexDisplacement r θ) -
          angularQuadraticPole d (windingTau (d + 1)) h r‖ / D ≤
        (k : ℝ) / 8 * Real.log (1 + x) := by
  dsimp only
  let h := firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
    (Real.cos φ) (Real.sin φ)
  have hN : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos d
  have hN0 : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
  have hk0 : 0 < (k : ℝ) := (sq_pos_of_pos hN0).trans_le hk
  have hτ := windingTau_pos (d + 1) (by omega)
  have hτbounds := windingTau_bounds (d + 1) (by omega)
  have hQ1 : r ^ 2 ≤ 1 := by nlinarith
  obtain ⟨hx, hxlo, hxhi⟩ := radial_outer_region hN hk0 hτ (sq_nonneg r) hQ1
    hτbounds.1 hτbounds.2 p.curvature_re hupper hA houter
  intro θ
  have hQ : displacementSquare (d + 1) (angularComplexDisplacement r θ) < σ ^ 2 := by
    rw [angularComplexDisplacement_square]
    nlinarith
  have hell : ‖p.densityLog (angularComplexDisplacement r θ)‖ ≤
      Kρ * (Real.sqrt (((d + 1 : ℕ) : ℝ) * r ^ 2) + ((d + 1 : ℕ) : ℝ) * r ^ 2) := by
    simpa only [angularComplexDisplacement_square] using p.log_bound _ hQ
  have hdensity := radial_density_bound hN0 hτ (sq_nonneg r) hτbounds.1 hτbounds.2
    p.curvature_re hupper hKρ hell
  have hR := higher_pole_error_small_strong (d + 1) (by omega) (angularComplexDisplacement r θ)
    hKp hσ hσ1 hKσ hQ (p.pole_error _ hQ)
  rw [angular_quadratic_identity, angularComplexDisplacement_square] at hR
  apply full_tail_log_absorption hN hk (sq_nonneg r) p.curvature_re hτ hx
    (by field_simp : windingTau (d + 1) *
      (h.re * r ^ 2 / (2 * ((d + 1 : ℕ) : ℝ) * windingTau (d + 1))) =
      h.re * r ^ 2 / (2 * ((d + 1 : ℕ) : ℝ))) hxlo hxhi
    (by positivity : 0 ≤ Kρ * (1 + 2 * Real.pi ^ 2)) hlarge hdensity hR

end PhysicalFirstWindingData

theorem exists_physical_first_winding_data_for_full_radial_split
    {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ0 : 0 < φ) (hφpi : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ σ C Kρ Kp : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < C ∧ 0 < Kρ ∧ 0 < Kp ∧
      768 * Kp * σ ≤ 1 ∧
      ∀ᶠ n : ℕ in atTop,
        Nonempty (PhysicalFirstWindingData b B φ n σ C Kρ Kp) ∧
        (firstWindingCurvature n (B (windingTau n : ℂ)) (Real.cos φ) (Real.sin φ)).re ≤ 2 ∧
        64 * (Kρ * (1 + 2 * Real.pi ^ 2)) ≤ (n : ℝ) := by
  obtain ⟨σ₀, C, Kρ, Kp, hσ₀, hσ₀1, hC, hKρ, hKp, _, he⟩ :=
    exists_physical_first_winding_data hb hB hφ0 hφpi hBi hbsq
  let σ := min σ₀ (1 / (768 * Kp))
  have hσ : 0 < σ := lt_min hσ₀ (by positivity)
  have hσ₀' : σ ≤ σ₀ := min_le_left _ _
  have hKσ : 768 * Kp * σ ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 768 * Kp)).mp (min_le_right σ₀ (1 / (768 * Kp)))
    nlinarith
  have hu : ∀ᶠ n : ℕ in atTop,
      (firstWindingCurvature n (B (windingTau n : ℂ)) (Real.cos φ) (Real.sin φ)).re ≤ 2 := by
    have hh := Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_firstWindingCurvature_one B hB.continuousAt (Real.cos φ) (Real.sin φ))
    exact hh.eventually (eventually_le_nhds (by norm_num : (1 : ℂ).re < 2))
  have hn : ∀ᶠ n : ℕ in atTop, 64 * (Kρ * (1 + 2 * Real.pi ^ 2)) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  refine ⟨σ, C, Kρ, Kp, hσ, hσ₀'.trans hσ₀1, hC, hKρ, hKp, hKσ, ?_⟩
  filter_upwards [he, hu, hn] with n hp hupper hlarge
  obtain ⟨p⟩ := hp
  exact ⟨⟨p.restrictRadius hσ hσ₀'⟩, hupper, hlarge⟩

end
end IsingBulk.AnisoF002.NegativeHT
