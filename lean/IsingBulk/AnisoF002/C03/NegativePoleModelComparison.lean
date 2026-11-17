import IsingBulk.AnisoF002.C03.NegativeActualPoleIntegral
import IsingBulk.AnisoF002.C03.NegativeModelBranchSign

/-!
# The actual first-winding integral and the exact frozen model

The physical center density is evaluated on the same global phase as the
complete coefficient.  The full real-plane period then gives the literal
frozen model, including its factorial, beta quotient and independent-chart
Jacobian.  The physical square-root branch contributes one common sign.
The later pole-extraction theorem supplies the rational resonance and the
identification with Taylor coefficients of the complete original series.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory Angular
open scoped Topology

theorem eventually_global_center_density {b B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ0 : 0 < φ) (hφpi : φ < Real.pi)
    (hBi : (B 0).im < 0) (hbsq : ∀ t, b t ^ 2 = B t) :
    ∀ᶠ n : ℕ in atTop, Odd n →
      filledNegativeDensityAt n b (negativeGlobalPhase B φ)
        ((Real.pi / (n : ℝ) : ℝ) : ℂ) (windingTau n : ℂ) 0 =
          centerDensityScalar n (b (windingTau n : ℂ)) (Real.sin φ) := by
  have hB0 : B 0 ≠ 0 := by intro he; simp [he] at hBi
  have hφ : Real.sin φ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hφ0 hφpi).ne'
  have hBc : ∀ᶠ n : ℕ in atTop,
      AnalyticAt ℂ B (windingTau n : ℂ) ∧ B (windingTau n : ℂ) ≠ 0 :=
    ((continuous_fst.continuousAt : ContinuousAt (fun p : ℂ × ℂ => p.1) (0, 0)).tendsto.comp
      tendsto_complex_winding_centers).eventually
      (hB.eventually_analyticAt.and (hB.continuousAt.eventually_ne hB0))
  have hg := eventually_uniform_negative_phase_centers
    (negativeGlobalPhase_analyticAt_zero hB hφ0 hφpi)
      (negativeGlobalPhase_center B hφ0 hφpi)
  filter_upwards [hBc, hg, eventually_ge_atTop (2 : ℕ)] with n hnB hng hn
  intro hodd
  simpa only [windingTau, centerDensityScalar] using
    filledNegativeDensity_exact_center n hodd hn b B (negativeGlobalPhase B φ) φ
      (Real.pi / (n : ℝ)) hφ hnB.1 hnB.2 (hbsq _) hng.1 hng.2
        (Filter.Eventually.of_forall (negativeGlobalPhase_cosh B φ))

theorem eventually_global_center_root_sign {b B : ℂ → ℂ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hBi : (B 0).im < 0) (hbsq : ∀ t, b t ^ 2 = B t) :
    ‖Complex.sqrt (B 0) / b 0‖ = 1 ∧
      ∀ᶠ n : ℕ in atTop,
        Complex.sqrt (B (windingTau n : ℂ)) / b (windingTau n : ℂ) =
          Complex.sqrt (B 0) / b 0 := by
  have hslit : B 0 ∈ Complex.slitPlane := Or.inr (ne_of_lt hBi)
  refine ⟨physical_root_branch_sign_norm (Complex.slitPlane_ne_zero hslit) (hbsq 0), ?_⟩
  obtain ⟨r, hr, hsign⟩ := exists_common_physical_root_sign hB hb hslit hbsq
  have ht : Tendsto (fun n : ℕ => (windingTau n : ℂ)) atTop (𝓝 (0 : ℂ)) :=
    (continuous_fst.continuousAt : ContinuousAt (fun p : ℂ × ℂ => p.1) (0, 0)).tendsto.comp
      tendsto_complex_winding_centers
  exact (ht.eventually (Metric.ball_mem_nhds _ hr)).mono (fun n hn => hsign _ hn)

namespace PhysicalFirstWindingData

variable {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {l : ℕ}
variable (p : PhysicalFirstWindingData b B φ (2 * l + 1) σ C Kρ Kp)

theorem twice_full_center_period_exact_model (hl : 0 < l) (m : ℕ)
    (hcenter : p.physicalCenterDensity =
      centerDensityScalar (2 * l + 1) (b (windingTau (2 * l + 1) : ℂ)) (Real.sin φ))
    (hB : B (windingTau (2 * l + 1) : ℂ) ≠ 0)
    (hbsq : b (windingTau (2 * l + 1) : ℂ) ^ 2 = B (windingTau (2 * l + 1) : ℂ))
    (hφ : Real.sin φ ≠ 0) :
    2 * p.physicalCenterDensity * p.fullQuadraticPeriod (2 * l * (l + 1) + m + 1) =
      (Complex.sqrt (B (windingTau (2 * l + 1) : ℂ)) / b (windingTau (2 * l + 1) : ℂ)) *
        modelCoefficient (2 * l + 1) (2 * l * (l + 1) + m)
          (B (windingTau (2 * l + 1) : ℂ))
          (firstWindingCurvature (2 * l + 1) (B (windingTau (2 * l + 1) : ℂ))
            (Real.cos φ) (Real.sin φ)) (Real.sin φ) (windingTau (2 * l + 1)) := by
  rw [hcenter, p.fullQuadraticPeriod_eq_actual]
  apply twice_center_quadratic_period_model hl m hB hbsq hφ
    (windingTau_pos (2 * l + 1) (by omega))
  have hr := p.curvature_re
  linarith

theorem twice_physical_residue_model_error (hl : 0 < l) (m : ℕ)
    (hcenter : p.physicalCenterDensity =
      centerDensityScalar (2 * l + 1) (b (windingTau (2 * l + 1) : ℂ)) (Real.sin φ))
    (hB : B (windingTau (2 * l + 1) : ℂ) ≠ 0)
    (hbsq : b (windingTau (2 * l + 1) : ℂ) ^ 2 = B (windingTau (2 * l + 1) : ℂ))
    (hφ : Real.sin φ ≠ 0) {R ε : ℝ} (hσ : 0 < σ) (hR : R < σ)
    (he : ‖p.compactPoleIntegral (2 * l * (l + 1) + m + 1) R -
        p.fullQuadraticPeriod (2 * l * (l + 1) + m + 1)‖ ≤
      ε * ‖p.fullQuadraticPeriod (2 * l * (l + 1) + m + 1)‖) :
    let M := modelCoefficient (2 * l + 1) (2 * l * (l + 1) + m)
      (B (windingTau (2 * l + 1) : ℂ))
      (firstWindingCurvature (2 * l + 1) (B (windingTau (2 * l + 1) : ℂ))
        (Real.cos φ) (Real.sin φ)) (Real.sin φ) (windingTau (2 * l + 1))
    ‖2 * p.physicalResidueIntegral (2 * l * (l + 1) + m + 1) R -
        (Complex.sqrt (B (windingTau (2 * l + 1) : ℂ)) / b (windingTau (2 * l + 1) : ℂ)) * M‖ ≤
      ε * ‖M‖ := by
  dsimp only
  rw [← p.twice_full_center_period_exact_model hl m hcenter hB hbsq hφ]
  have hp := p.physicalResidueIntegral_relative_error hσ hR he
  have hsign := physical_root_branch_sign_norm hB hbsq
  have hmod := congrArg norm (p.twice_full_center_period_exact_model hl m hcenter hB hbsq hφ)
  conv_rhs at hmod => rw [norm_mul, hsign, one_mul]
  have hleft : 2 * p.physicalResidueIntegral (2 * l * (l + 1) + m + 1) R -
      2 * p.physicalCenterDensity * p.fullQuadraticPeriod (2 * l * (l + 1) + m + 1) =
      2 * (p.physicalResidueIntegral (2 * l * (l + 1) + m + 1) R -
        p.physicalCenterDensity * p.fullQuadraticPeriod (2 * l * (l + 1) + m + 1)) := by ring
  rw [hleft, norm_mul]
  have he2 := mul_le_mul_of_nonneg_left hp (norm_nonneg (2 : ℂ))
  calc
    _ ≤ ‖(2 : ℂ)‖ * (ε * ‖p.physicalCenterDensity *
        p.fullQuadraticPeriod (2 * l * (l + 1) + m + 1)‖) := he2
    _ = ε * ‖2 * p.physicalCenterDensity *
        p.fullQuadraticPeriod (2 * l * (l + 1) + m + 1)‖ := by
      simp only [norm_mul]
      ring
    _ = _ := by rw [hmod]

end PhysicalFirstWindingData
end
end IsingBulk.AnisoF002.NegativeHT
