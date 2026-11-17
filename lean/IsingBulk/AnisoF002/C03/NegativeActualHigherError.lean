import IsingBulk.AnisoF002.C03.NegativeUniformHigherPole
import IsingBulk.AnisoF002.C03.NegativeCurvatureRatio
import IsingBulk.AnisoF002.C03.NegativeActualDensity

/-!
# Frozen (4.8) for the actual negative-edge phase

The exact spectral curvature is identified with the actual derivative
ratio.  A single radius is chosen before n, and every phase zero with the
constructed coarse bound satisfies the complete higher-order estimate.
Consequently this applies to the very same analytic T used in the full
physical residue density, without selecting a new branch or a new pole.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 2000000 in
theorem exists_actual_phase_higher_error {B : ℂ → ℂ} {g : ℂ × ℂ → ℂ} {φ : ℝ}
    (hφ : Real.sin φ ≠ 0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0)
    (hg : AnalyticAt ℂ g (0, 0))
    (hcenter : ∀ δ : ℂ, g (1 - Complex.cos δ, δ) = (φ : ℂ) * Complex.I)
    (heven : ∀ t d : ℂ, g (t, -d) = g (t, d))
    (hdisp : ∀ᶠ a in 𝓝 (0, 0), Complex.cosh (g a) = localNegativeDispersion B φ a)
    {C : ℝ} (hC : 0 < C) :
    ∃ σ K : ℝ, 0 < σ ∧ 0 < K ∧
      ∀ᶠ n : ℕ in atTop, ∀ v : Fin n → ℂ,
        (∑ i, v i) = 0 → displacementSquare n v < σ ^ 2 →
        ∀ t : ℂ,
          (∑ i, g (t, ((Real.pi / (n : ℝ) : ℝ) : ℂ) + v i)) =
            (n : ℂ) * ((φ : ℂ) * Complex.I) →
          ‖t - (windingTau n : ℂ)‖ ≤ C * displacementSquare n v / (n : ℝ) →
          ‖t - ((windingTau n : ℂ) +
            firstWindingCurvature n (B (windingTau n : ℂ)) (Real.cos φ) (Real.sin φ) *
              (∑ i, v i ^ 2) / (2 * (n : ℂ)))‖ ≤
            K / (n : ℝ) * ((∑ i, ‖v i‖ ^ 3) / (n : ℝ) +
              (∑ i, ‖v i‖ ^ 4) + displacementSquare n v ^ 2 / (n : ℝ)) := by
  have hg0 : g (0, 0) = (φ : ℂ) * Complex.I := by simpa using hcenter 0
  have hc : phaseTemperatureDerivative g (0, 0) ≠ 0 :=
    physical_negative_phase_temperature_derivative_ne_zero hφ hB hB0 hg hg0 hdisp
  obtain ⟨r, K, hr, hK, herror⟩ := exists_uniform_higher_pole_error hg hc heven hC
  let σ : ℝ := min (r / 4) (min 1 (r / (4 * C)))
  have hσ : 0 < σ := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hσr : σ ≤ r / 4 := min_le_left _ _
  have hσ1 : σ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hσfrac : σ ≤ r / (4 * C) := (min_le_right _ _).trans (min_le_right _ _)
  have hσC : C * σ ^ 2 ≤ r / 4 := by
    have hfrac := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hσfrac
    have hsq : σ ^ 2 ≤ σ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq hC.le]
  have hsmall : ∀ᶠ n : ℕ in atTop,
      ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ)) ∈ Metric.ball (0, 0) (r / 4) :=
    tendsto_complex_winding_centers.eventually (Metric.ball_mem_nhds _ (by positivity))
  have hBcent : ∀ᶠ n : ℕ in atTop,
      AnalyticAt ℂ B (windingTau n : ℂ) ∧ B (windingTau n : ℂ) ≠ 0 :=
    ((continuous_fst.continuousAt : ContinuousAt (fun p : ℂ × ℂ => p.1) (0, 0)).tendsto.comp
      tendsto_complex_winding_centers).eventually
      (hB.eventually_analyticAt.and (hB.continuousAt.eventually_ne hB0))
  have hgcent := tendsto_complex_winding_centers.eventually hg.eventually_analyticAt
  have hecent := tendsto_complex_winding_centers.eventually hdisp.eventually_nhds
  refine ⟨σ, K, hσ, hK, ?_⟩
  filter_upwards [hsmall, hBcent, hgcent, hecent, eventually_gt_atTop (0 : ℕ)]
    with n hnsmall hnB hng hnhe hn
  have hcen : g ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ)) =
      (φ : ℂ) * Complex.I := by
    simpa only [windingTau, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cos] using
      hcenter ((Real.pi / (n : ℝ) : ℝ) : ℂ)
  have hratio := first_winding_angular_ratio n B φ hφ hnB.1 hnB.2 hng hcen hnhe
  have hcenNorm : ‖(windingTau n : ℂ)‖ < r / 4 ∧
      ‖((Real.pi / (n : ℝ) : ℝ) : ℂ)‖ < r / 4 := by
    simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def] using hnsmall
  intro v hsum hQ t hphase hcoarse
  obtain ⟨hp, hq, hv⟩ := coarse_pole_points_in_common_ball hn hr hσ hC.le hσr hσC
    hcenNorm.1 hcenNorm.2 hQ hcoarse
  have hd : ‖((Real.pi / (n : ℝ) : ℝ) : ℂ)‖ ≤ Real.pi / (n : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hh := herror n hn (windingTau n : ℂ) ((Real.pi / (n : ℝ) : ℝ) : ℂ) t v
    hsum hp hq hv (by simpa only [hcen] using hphase) hcoarse hd
  rw [hratio] at hh
  convert hh using 1
  congr 1
  ring

theorem real_displacement_square (n : ℕ) (v : Fin n → ℝ) :
    displacementSquare n (fun i => (v i : ℂ)) = ∑ i, v i ^ 2 := by
  unfold displacementSquare
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem real_complex_sum_squares (n : ℕ) (v : Fin n → ℝ) :
    (∑ i, (v i : ℂ) ^ 2) = ((∑ i, v i ^ 2 : ℝ) : ℂ) := by
  simp

end
end IsingBulk.AnisoF002.NegativeHT
