import IsingBulk.AnisoF002.C03.NegativePoleDensityBridge
import IsingBulk.AnisoF002.C03.NegativePhysicalSquareRoot

/-!
# The uniform full residue density for the actual negative-edge dispersion

The phase, parameter inverse, spectral ratio, constrained pole and full
filled density are constructed in one statement.  Every prescribed
square-root center normalization is preserved.  Identification of the
resulting coefficient integrals with the full physical susceptibility
and full-series noncancellation are separate remaining obligations.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry Set Filter
open scoped Topology BigOperators

set_option maxHeartbeats 2000000 in
theorem exists_actual_negative_complete_density {lam φ : ℝ} {z : ℂ}
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
        ∃ σ C K : ℝ, 0 < σ ∧ 0 < C ∧ 0 < K ∧
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
              ‖ell v‖ ≤ K * (Real.sqrt ((n : ℝ) * displacementSquare n (v : Fin n → ℂ)) +
                (n : ℝ) * displacementSquare n (v : Fin n → ℂ)) := by
  obtain ⟨Z, B, g, hZa, hZ0, hBa, hB0, hBne, hBe, hgcenter, heven,
    ⟨r, hr, hphysical⟩, hroot, hright, hleft⟩ :=
    exists_uniform_negative_physical_phase hlam hx hφ0 hφpi hinc hside
  have hsin : Real.sin φ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ0 hφpi)
  have hγ : Complex.sinh ((φ : ℂ) * Complex.I) ≠ 0 := by
    rw [Complex.sinh_mul_I, ← Complex.ofReal_sin]
    exact mul_ne_zero (by exact_mod_cast hsin) Complex.I_ne_zero
  have hg : AnalyticAt ℂ g (0, 0) := (hphysical (0, 0) (Metric.mem_ball_self hr)).1
  have hg0 : g (0, 0) = (φ : ℂ) * Complex.I := by simpa using hgcenter 0
  have hball : ∀ᶠ a : ℂ × ℂ in 𝓝 (0, 0), a ∈ Metric.ball (0, 0) r :=
    Metric.ball_mem_nhds _ hr
  have he : ∀ᶠ a in 𝓝 (0, 0), Complex.cosh (g a) = localNegativeDispersion B φ a :=
    hball.mono (fun a ha => (hphysical a ha).2.2.1)
  have hc := physical_negative_phase_temperature_derivative_ne_zero hsin hBa hBne hg hg0 he
  refine ⟨Z, B, g, hZa, hZ0, hBa, hB0, hBne, hBe, hgcenter, heven,
    ⟨r, hr, hphysical⟩, hroot, hright, hleft, ?_⟩
  intro b₀ hb₀
  have hba := normalizedLocalSquareRoot_analyticAt b₀ hBa hBne
  refine ⟨hba, normalizedLocalSquareRoot_center b₀ hBne,
    normalizedLocalSquareRoot_sq hBne hb₀, ?_⟩
  exact exists_uniform_poles_and_complete_density hba
    (normalizedLocalSquareRoot_center_ne_zero hBne hb₀) hg hc hgcenter heven hγ

end
end IsingBulk.AnisoF002.NegativeHT
