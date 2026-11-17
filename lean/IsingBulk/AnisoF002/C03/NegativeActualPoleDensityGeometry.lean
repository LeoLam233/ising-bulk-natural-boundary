import IsingBulk.AnisoF002.C03.NegativeActualHigherError

/-!
# The same physical pole, complete residue and higher geometry

This joins frozen (4.7), (4.8) and the full-density logarithm (4.13) for
one constructed phase and one analytic constrained pole.  The physical
spectral ratio, canonical inward branch, inverse parameter and prescribed
square-root normalization are all retained from the actual chart.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 2000000 in
theorem exists_actual_negative_pole_density_geometry {lam φ : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0) (hφ0 : 0 < φ) (hφpi : φ < Real.pi)
    (hinc : spectralA lam z = spectralS z * (Real.cos φ : ℂ) + spectralT lam z * (-1))
    (hside : (spectralT lam z / spectralS z).im < 0) :
    ∃ (Z B : ℂ → ℂ) (g : ℂ × ℂ → ℂ),
      AnalyticAt ℂ Z 0 ∧ Z 0 = z ∧ AnalyticAt ℂ B 0 ∧
      B 0 = spectralT lam z / spectralS z ∧ B 0 ≠ 0 ∧
      (∀ t, B t = spectralT lam (Z t) / spectralS (Z t)) ∧
      (∀ δ : ℂ, g (1 - Complex.cos δ, δ) = (φ : ℂ) * Complex.I) ∧
      (∀ t δ : ℂ, g (t, -δ) = g (t, δ)) ∧
      (∃ r : ℝ, 0 < r ∧ ∀ a ∈ Metric.ball (0, 0) r,
        AnalyticAt ℂ g a ∧ spectralS (Z a.1) ≠ 0 ∧
        Complex.cosh (g a) = localNegativeDispersion B φ a ∧
        Complex.cosh (g a) =
          (spectralA lam (Z a.1) - spectralT lam (Z a.1) *
            Complex.cos ((Real.pi : ℂ) + a.2)) / spectralS (Z a.1)) ∧
      (∀ᶠ a : ℝ × ℝ in 𝓝 (0, 0), a.1 < 0 →
        0 < (g (realPairToComplex a)).re ∧
        Complex.exp (-g (realPairToComplex a)) =
          spectralSmallRootF002 lam (Z (a.1 : ℂ)) (Real.pi + a.2)) ∧
      (∀ᶠ t in 𝓝 0, negativeParameterF002 lam (Real.cos φ) (Z t) = t) ∧
      (∀ᶠ w in 𝓝 z, Z (negativeParameterF002 lam (Real.cos φ) w) = w) ∧
      ∀ b₀ : ℂ, b₀ ^ 2 = B 0 →
        let b := normalizedLocalSquareRoot B b₀
        AnalyticAt ℂ b 0 ∧ b 0 = b₀ ∧ (∀ t : ℂ, b t ^ 2 = B t) ∧
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
  obtain ⟨Z, B, g, hZa, hZ0, hBa, hB0, hBne, hBe, hgcenter, heven,
    ⟨r, hr, hphysical⟩, hroot, hright, hleft, hdensity⟩ :=
    exists_actual_negative_complete_density hlam hx hφ0 hφpi hinc hside
  have hsin : Real.sin φ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ0 hφpi)
  have hg : AnalyticAt ℂ g (0, 0) := (hphysical (0, 0) (Metric.mem_ball_self hr)).1
  have hball : ∀ᶠ a : ℂ × ℂ in 𝓝 (0, 0), a ∈ Metric.ball (0, 0) r :=
    Metric.ball_mem_nhds _ hr
  have he : ∀ᶠ a in 𝓝 (0, 0), Complex.cosh (g a) = localNegativeDispersion B φ a :=
    hball.mono (fun a ha => (hphysical a ha).2.2.1)
  refine ⟨Z, B, g, hZa, hZ0, hBa, hB0, hBne, hBe, hgcenter, heven,
    ⟨r, hr, hphysical⟩, hroot, hright, hleft, ?_⟩
  intro b₀ hb₀
  obtain ⟨hba, hbvalue, hbsq, σ₀, C, Kρ, hσ₀, hC, hKρ, hdens⟩ := hdensity b₀ hb₀
  obtain ⟨σ₁, Kp, hσ₁, hKp, herr⟩ :=
    exists_actual_phase_higher_error hsin hBa hBne hg hgcenter heven he hC
  let σ := min σ₀ σ₁
  have hσ : 0 < σ := lt_min hσ₀ hσ₁
  have hσ₀' : σ ≤ σ₀ := min_le_left _ _
  have hσ₁' : σ ≤ σ₁ := min_le_right _ _
  refine ⟨hba, hbvalue, hbsq, σ, C, Kρ, Kp, hσ, hC, hKρ, hKp, ?_⟩
  filter_upwards [hdens, herr] with n hnρ hnp
  obtain ⟨T, ell, hTa, hT0, hv⟩ := hnρ
  refine ⟨T, ell, (fun v hv' => hTa v (Metric.ball_subset_ball hσ₀' hv')), hT0, ?_⟩
  intro v hQ
  have hQ₀ : displacementSquare n (v : Fin n → ℂ) < σ₀ ^ 2 :=
    hQ.trans_le (by nlinarith)
  have hQ₁ : displacementSquare n (v : Fin n → ℂ) < σ₁ ^ 2 :=
    hQ.trans_le (by nlinarith)
  obtain ⟨hphase, hcoarse, hderiv, hella, hnonzero, hfactor, hlog⟩ := hv v hQ₀
  refine ⟨hphase, hcoarse, hderiv, hella, hnonzero, hfactor, hlog, ?_⟩
  exact hnp (v : Fin n → ℂ) (zeroSumDisplacements_sum v) hQ₁ (T v) hphase hcoarse

end
end IsingBulk.AnisoF002.NegativeHT
