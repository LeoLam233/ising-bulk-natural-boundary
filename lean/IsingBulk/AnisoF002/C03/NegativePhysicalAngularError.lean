import IsingBulk.AnisoF002.C03.NegativeGlobalPoleDensity
import IsingBulk.AnisoF002.C03.NegativeAngularPoleError

/-!
# The averaged error for the actual full physical first-winding residue

The data below are constructed from the physical analytic anisotropy
factor and its square root.  They are not an added physical premise.
The same global phase serves the complete real-cycle coefficients,
the exact moving pole, and its full Vandermonde residue density.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

theorem eventually_firstWindingCurvature_re_half (B : ℂ → ℂ)
    (hB : ContinuousAt B 0) (b s : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) ≤ (firstWindingCurvature n (B (windingTau n : ℂ)) b s).re := by
  have hb : ∀ᶠ n : ℕ in atTop, ‖B (windingTau n : ℂ)‖ ≤ ‖B 0‖ + 1 :=
    (tendsto_anisotropy_at_centers B hB).norm.eventually (eventually_le_nhds (by linarith))
  have hn2 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hl : ∀ᶠ n : ℕ in atTop,
      2 * curvatureErrorConstant (‖B 0‖ + 1) b s ≤ (n : ℝ) ^ 2 :=
    hn2.eventually (eventually_ge_atTop _)
  filter_upwards [hb, hl, eventually_gt_atTop (0 : ℕ)] with n hbn hln hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he := firstWindingCurvature_uniform_bound n (B (windingTau n : ℂ)) b s
    (‖B 0‖ + 1) hn hbn
  have he' : ‖firstWindingCurvature n (B (windingTau n : ℂ)) b s - 1‖ ≤ 1 / 2 := by
    apply he.trans
    apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ) ^ 2)).mpr
    dsimp [curvatureErrorConstant] at hln
    nlinarith
  have hr := (Complex.abs_re_le_norm
    (firstWindingCurvature n (B (windingTau n : ℂ)) b s - 1)).trans he'
  simp only [Complex.sub_re, Complex.one_re] at hr
  have hh := (abs_le.mp hr).1
  linarith

structure PhysicalFirstWindingData (b B : ℂ → ℂ) (φ : ℝ) (n : ℕ)
    (σ C Kρ Kp : ℝ) where
  pole : zeroSumDisplacements n → ℂ
  densityLog : zeroSumDisplacements n → ℂ
  pole_analytic : AnalyticOnNhd ℂ pole (Metric.ball 0 σ)
  pole_center : pole 0 = (windingTau n : ℂ)
  phase : ∀ v : zeroSumDisplacements n, displacementSquare n v < σ ^ 2 →
    (∑ i, negativeGlobalPhase B φ (pole v,
      ((Real.pi / (n : ℝ) : ℝ) : ℂ) + (v : Fin n → ℂ) i)) =
        (n : ℂ) * ((φ : ℂ) * Complex.I)
  pole_coarse : ∀ v : zeroSumDisplacements n, displacementSquare n v < σ ^ 2 →
    ‖pole v - (windingTau n : ℂ)‖ ≤ C * displacementSquare n v / (n : ℝ)
  phase_deriv_ne_zero : ∀ v : zeroSumDisplacements n, displacementSquare n v < σ ^ 2 →
    deriv (centeredPhaseAverage n (negativeGlobalPhase B φ) ((φ : ℂ) * Complex.I)
      ((Real.pi / (n : ℝ) : ℝ) : ℂ) (v : Fin n → ℂ)) (pole v) ≠ 0
  log_analytic : ∀ v : zeroSumDisplacements n,
    displacementSquare n v < σ ^ 2 → AnalyticAt ℂ densityLog v
  center_density_ne_zero :
    filledNegativeDensityAt n b (negativeGlobalPhase B φ)
      ((Real.pi / (n : ℝ) : ℝ) : ℂ) (windingTau n : ℂ) 0 ≠ 0
  density_identity : ∀ v : zeroSumDisplacements n, displacementSquare n v < σ ^ 2 →
    -(2 * completeNegativeNumerator n b (negativeGlobalPhase B φ)
        ((Real.pi / (n : ℝ) : ℝ) : ℂ) (pole v) (v : Fin n → ℂ)) /
      phaseTemperatureSum n (negativeGlobalPhase B φ)
        ((Real.pi / (n : ℝ) : ℝ) : ℂ) (pole v) (v : Fin n → ℂ) =
    filledNegativeDensityAt n b (negativeGlobalPhase B φ)
        ((Real.pi / (n : ℝ) : ℝ) : ℂ) (windingTau n : ℂ) 0 *
      complexVandermondeSquared n (v : Fin n → ℂ) * Complex.exp (densityLog v)
  log_bound : ∀ v : zeroSumDisplacements n, displacementSquare n v < σ ^ 2 →
    ‖densityLog v‖ ≤ Kρ * (Real.sqrt ((n : ℝ) * displacementSquare n v) +
      (n : ℝ) * displacementSquare n v)
  pole_error : ∀ v : zeroSumDisplacements n, displacementSquare n v < σ ^ 2 →
    ‖pole v - ((windingTau n : ℂ) +
      firstWindingCurvature n (B (windingTau n : ℂ)) (Real.cos φ) (Real.sin φ) *
        (∑ i, (v : Fin n → ℂ) i ^ 2) / (2 * (n : ℂ)))‖ ≤
      Kp / (n : ℝ) * ((∑ i, ‖(v : Fin n → ℂ) i‖ ^ 3) / (n : ℝ) +
        (∑ i, ‖(v : Fin n → ℂ) i‖ ^ 4) + displacementSquare n v ^ 2 / (n : ℝ))
  curvature_re : (1 / 2 : ℝ) ≤
    (firstWindingCurvature n (B (windingTau n : ℂ)) (Real.cos φ) (Real.sin φ)).re

theorem exists_physical_first_winding_data {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ0 : 0 < φ) (hφpi : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ σ C Kρ Kp : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < C ∧ 0 < Kρ ∧ 0 < Kp ∧
      48 * Kp * σ ≤ 1 ∧
      ∀ᶠ n : ℕ in atTop, Nonempty (PhysicalFirstWindingData b B φ n σ C Kρ Kp) := by
  obtain ⟨σ₀, C, Kρ, Kp, hσ₀, hC, hKρ, hKp, hp⟩ :=
    exists_global_poles_and_complete_density hb hB hφ0 hφpi hBi hbsq
  let σ := min σ₀ (min 1 (1 / (48 * Kp)))
  have hσ : 0 < σ := lt_min hσ₀ (lt_min zero_lt_one (by positivity))
  have hσ₀' : σ ≤ σ₀ := min_le_left _ _
  have hσ1 : σ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hσK : σ ≤ 1 / (48 * Kp) := (min_le_right _ _).trans (min_le_right _ _)
  have hKσ : 48 * Kp * σ ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 48 * Kp)).mp hσK
    nlinarith
  refine ⟨σ, C, Kρ, Kp, hσ, hσ1, hC, hKρ, hKp, hKσ, ?_⟩
  filter_upwards [hp, eventually_firstWindingCurvature_re_half B hB.continuousAt
    (Real.cos φ) (Real.sin φ)] with n hn hre
  obtain ⟨T, ell, hTa, hT0, hdata⟩ := hn
  have hQ (v : zeroSumDisplacements n) (hv : displacementSquare n v < σ ^ 2) :
      displacementSquare n v < σ₀ ^ 2 := hv.trans_le (by nlinarith)
  have hzero : displacementSquare n (0 : zeroSumDisplacements n) < σ₀ ^ 2 := by
    simpa [displacementSquare] using (sq_pos_of_pos hσ₀)
  refine ⟨{
    pole := T
    densityLog := ell
    pole_analytic := hTa.mono (Metric.ball_subset_ball hσ₀')
    pole_center := hT0
    phase := fun v hv => (hdata v (hQ v hv)).1
    pole_coarse := fun v hv => (hdata v (hQ v hv)).2.1
    phase_deriv_ne_zero := fun v hv => (hdata v (hQ v hv)).2.2.1
    log_analytic := fun v hv => (hdata v (hQ v hv)).2.2.2.1
    center_density_ne_zero := (hdata 0 hzero).2.2.2.2.1
    density_identity := fun v hv => (hdata v (hQ v hv)).2.2.2.2.2.1
    log_bound := fun v hv => (hdata v (hQ v hv)).2.2.2.2.2.2.1
    pole_error := fun v hv => (hdata v (hQ v hv)).2.2.2.2.2.2.2
    curvature_re := hre }⟩

namespace PhysicalFirstWindingData
open Angular

theorem complete_central_angular_comparison
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
    Integrable (fun θ : AngularSphere d =>
      Complex.exp (p.densityLog (angularComplexDisplacement r θ)) /
        p.pole (angularComplexDisplacement r θ) ^ k) (angularLaw d) ∧
    ‖∫ θ : AngularSphere d,
      (Complex.exp (p.densityLog (angularComplexDisplacement r θ)) /
        p.pole (angularComplexDisplacement r θ) ^ k -
        1 / angularQuadraticPole d (windingTau (d + 1)) h r ^ k) ∂angularLaw d‖ ≤
      angularPerturbationConstant * (2 * A ^ 2 * (Kρ + Kp)) * δ / D ^ k := by
  apply complete_angular_pole_comparison hd hk hσ hσ1 hKρ hKp hKσ hr hrσ hA
    hδ hδ1 hscale hcentral hsmall (windingTau_pos (d + 1) (by omega))
    (windingTau_bounds (d + 1) (by omega)).1 p.curvature_re p.pole p.densityLog
  · intro v hv
    exact p.pole_analytic v (zeroSumDisplacements_mem_ball_of_square_lt v hσ hv)
  · exact p.log_analytic
  · exact p.log_bound
  · exact p.pole_error

end PhysicalFirstWindingData
end
end IsingBulk.AnisoF002.NegativeHT
