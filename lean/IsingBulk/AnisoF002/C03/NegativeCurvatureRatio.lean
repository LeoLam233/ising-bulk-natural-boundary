import IsingBulk.AnisoF002.C03.NegativePhaseCurvature

/-!
# Exact ratio of the center phase derivatives

The scalar multiplying the constrained quadratic form is the literal
first-winding curvature, with B evaluated at the exact center.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped Topology

theorem negative_center_angular_ratio (B : ℂ → ℂ) (φ d : ℝ)
    (hφ : Real.sin φ ≠ 0)
    (hB : AnalyticAt ℂ B ((1 - Real.cos d : ℝ) : ℂ))
    (hBne : B ((1 - Real.cos d : ℝ) : ℂ) ≠ 0)
    {g : ℂ × ℂ → ℂ}
    (hga : AnalyticAt ℂ g ((1 - Real.cos d : ℝ), (d : ℂ)))
    (hgv : g ((1 - Real.cos d : ℝ), (d : ℂ)) = (φ : ℂ) * Complex.I)
    (hge : ∀ᶠ a in 𝓝 ((1 - Real.cos d : ℝ), (d : ℂ)),
      Complex.cosh (g a) = localNegativeDispersion B φ a) :
    angularJet 2 g ((1 - Real.cos d : ℝ), (d : ℂ)) /
      (2 * phaseTemperatureDerivative g ((1 - Real.cos d : ℝ), (d : ℂ))) =
      -((Real.cos d : ℂ) - B ((1 - Real.cos d : ℝ) : ℂ) * (Real.cos φ : ℂ) /
        (Real.sin φ : ℂ) ^ 2 * (Real.sin d : ℂ) ^ 2) / 2 := by
  have hd := local_negative_phase_derivative_unique B φ d hφ hB hga hgv hge
  have hc : phaseTemperatureDerivative g ((1 - Real.cos d : ℝ), (d : ℂ)) =
      ((Real.sin φ : ℂ) * Complex.I)⁻¹ * B ((1 - Real.cos d : ℝ) : ℂ) := by
    simpa [phaseTemperatureDerivative] using
      congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L (1, 0)) hd.fderiv
  rw [negative_center_angular_curvature B φ d hφ hga hgv hge, hc]
  have hs : (Real.sin φ : ℂ) ≠ 0 := by exact_mod_cast hφ
  field_simp
  ring_nf
  norm_num

theorem first_winding_angular_ratio (n : ℕ) (B : ℂ → ℂ) (φ : ℝ)
    (hφ : Real.sin φ ≠ 0) (hB : AnalyticAt ℂ B (windingTau n : ℂ))
    (hBne : B (windingTau n : ℂ) ≠ 0) {g : ℂ × ℂ → ℂ}
    (hga : AnalyticAt ℂ g ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ)))
    (hgv : g ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ)) = (φ : ℂ) * Complex.I)
    (hge : ∀ᶠ a in 𝓝 ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ)),
      Complex.cosh (g a) = localNegativeDispersion B φ a) :
    angularJet 2 g ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ)) /
      (2 * phaseTemperatureDerivative g ((windingTau n : ℂ), ((Real.pi / (n : ℝ) : ℝ) : ℂ))) =
      -firstWindingCurvature n (B (windingTau n : ℂ)) (Real.cos φ) (Real.sin φ) / 2 :=
  negative_center_angular_ratio B φ (Real.pi / (n : ℝ)) hφ hB hBne hga hgv hge

end
end IsingBulk.AnisoF002.NegativeHT
