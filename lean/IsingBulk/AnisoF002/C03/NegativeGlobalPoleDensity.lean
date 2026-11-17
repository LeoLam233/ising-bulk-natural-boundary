import IsingBulk.AnisoF002.C03.NegativeGlobalPhysicalChart

/-!
# One global physical phase for coefficient disks and first-winding residues

The uniform pole/density construction is instantiated on the same explicit
global phase used in every complete coefficient integral.  Thus no change
of the logarithmic branch separates the real-cycle residue estimates from
the full boundary-jet family.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 2000000 in
theorem exists_global_poles_and_complete_density {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ0 : 0 < φ) (hφpi : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    let g := negativeGlobalPhase B φ
    ∃ σ C Kρ Kp : ℝ, 0 < σ ∧ 0 < C ∧ 0 < Kρ ∧ 0 < Kp ∧
      ∀ᶠ n : ℕ in atTop, ∃ T ell : zeroSumDisplacements n → ℂ,
        AnalyticOnNhd ℂ T (Metric.ball 0 σ) ∧ T 0 = (windingTau n : ℂ) ∧
        ∀ v : zeroSumDisplacements n, displacementSquare n (v : Fin n → ℂ) < σ ^ 2 →
          (∑ i, g (T v, ((Real.pi / (n : ℝ) : ℝ) : ℂ) + (v : Fin n → ℂ) i)) =
            (n : ℂ) * ((φ : ℂ) * Complex.I) ∧
          ‖T v - (windingTau n : ℂ)‖ ≤ C * displacementSquare n (v : Fin n → ℂ) / (n : ℝ) ∧
          deriv (centeredPhaseAverage n g ((φ : ℂ) * Complex.I)
            ((Real.pi / (n : ℝ) : ℝ) : ℂ) (v : Fin n → ℂ)) (T v) ≠ 0 ∧
          AnalyticAt ℂ ell v ∧
          filledNegativeDensityAt n b g ((Real.pi / (n : ℝ) : ℝ) : ℂ) (windingTau n : ℂ) 0 ≠ 0 ∧
          -(2 * completeNegativeNumerator n b g ((Real.pi / (n : ℝ) : ℝ) : ℂ) (T v) (v : Fin n → ℂ)) /
            phaseTemperatureSum n g ((Real.pi / (n : ℝ) : ℝ) : ℂ) (T v) (v : Fin n → ℂ) =
            filledNegativeDensityAt n b g ((Real.pi / (n : ℝ) : ℝ) : ℂ) (windingTau n : ℂ) 0 *
              complexVandermondeSquared n (v : Fin n → ℂ) * Complex.exp (ell v) ∧
          ‖ell v‖ ≤ Kρ * (Real.sqrt ((n : ℝ) * displacementSquare n (v : Fin n → ℂ)) +
            (n : ℝ) * displacementSquare n (v : Fin n → ℂ)) ∧
          ‖T v - ((windingTau n : ℂ) +
            firstWindingCurvature n (B (windingTau n : ℂ)) (Real.cos φ) (Real.sin φ) *
              (∑ i, (v : Fin n → ℂ) i ^ 2) / (2 * (n : ℂ)))‖ ≤
            Kp / (n : ℝ) * ((∑ i, ‖(v : Fin n → ℂ) i‖ ^ 3) / (n : ℝ) +
              (∑ i, ‖(v : Fin n → ℂ) i‖ ^ 4) +
                displacementSquare n (v : Fin n → ℂ) ^ 2 / (n : ℝ)) := by
  let g := negativeGlobalPhase B φ
  have hsin : Real.sin φ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ0 hφpi)
  have hB0 : B 0 ≠ 0 := by intro hz; simp [hz] at hBi
  have hb0 : b 0 ≠ 0 := by
    intro hz
    have he := hbsq 0
    rw [hz, zero_pow (by norm_num)] at he
    exact hB0 he.symm
  have hg : AnalyticAt ℂ g (0, 0) := negativeGlobalPhase_analyticAt_zero hB hφ0 hφpi
  have hgcenter : ∀ δ : ℂ, g (1 - Complex.cos δ, δ) = (φ : ℂ) * Complex.I :=
    negativeGlobalPhase_center B hφ0 hφpi
  have heven : ∀ t δ : ℂ, g (t, -δ) = g (t, δ) := negativeGlobalPhase_even B φ
  have hg0 : g (0, 0) = (φ : ℂ) * Complex.I := by simpa using hgcenter 0
  have he : ∀ᶠ a in 𝓝 (0, 0), Complex.cosh (g a) = localNegativeDispersion B φ a :=
    Filter.Eventually.of_forall (negativeGlobalPhase_cosh B φ)
  have hc := physical_negative_phase_temperature_derivative_ne_zero hsin hB hB0 hg hg0 he
  have hγ : Complex.sinh ((φ : ℂ) * Complex.I) ≠ 0 := by
    rw [Complex.sinh_mul_I, ← Complex.ofReal_sin]
    exact mul_ne_zero (by exact_mod_cast hsin) Complex.I_ne_zero
  obtain ⟨σ₀, C, Kρ, hσ₀, hC, hKρ, hdensity⟩ :=
    exists_uniform_poles_and_complete_density hb hb0 hg hc hgcenter heven hγ
  obtain ⟨σ₁, Kp, hσ₁, hKp, herr⟩ :=
    exists_actual_phase_higher_error hsin hB hB0 hg hgcenter heven he hC
  let σ := min σ₀ σ₁
  have hσ : 0 < σ := lt_min hσ₀ hσ₁
  have hσ₀' : σ ≤ σ₀ := min_le_left _ _
  have hσ₁' : σ ≤ σ₁ := min_le_right _ _
  refine ⟨σ, C, Kρ, Kp, hσ, hC, hKρ, hKp, ?_⟩
  filter_upwards [hdensity, herr] with n hnρ hnp
  obtain ⟨T, ell, hTa, hT0, hv⟩ := hnρ
  refine ⟨T, ell, hTa.mono (Metric.ball_subset_ball hσ₀'), hT0, ?_⟩
  intro v hQ
  have hQ₀ : displacementSquare n (v : Fin n → ℂ) < σ₀ ^ 2 := hQ.trans_le (by nlinarith)
  have hQ₁ : displacementSquare n (v : Fin n → ℂ) < σ₁ ^ 2 := hQ.trans_le (by nlinarith)
  obtain ⟨hphase, hcoarse, hderiv, hella, hnonzero, hfactor, hlog⟩ := hv v hQ₀
  exact ⟨hphase, hcoarse, hderiv, hella, hnonzero, hfactor, hlog,
    hnp (v : Fin n → ℂ) (zeroSumDisplacements_sum v) hQ₁ (T v) hphase hcoarse⟩

end
end IsingBulk.AnisoF002.NegativeHT
