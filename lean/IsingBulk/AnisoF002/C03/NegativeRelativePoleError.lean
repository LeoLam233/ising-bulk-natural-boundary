import IsingBulk.AnisoF002.C03.NegativePositivePeriod

/-!
# Relative error for the actual complete first-winding pole integral

The positive beta normalizer is the actual period with real curvature.
Its comparison with the complex period costs only the explicit uniform
phase factor.  Thus the full angular and radial error is relative to the
same nonzero complex period that enters the exact physical coefficient.
-/

namespace IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
noncomputable section
open MeasureTheory Set Angular

variable {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {d : ℕ}
variable (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)

theorem fullQuadraticPeriod_norm_pos {k : ℕ} (hd : 0 < d)
    (hα : radialShape d = (particleExponent (d + 1) : ℝ))
    (hk : particleExponent (d + 1) < k) : 0 < ‖p.fullQuadraticPeriod k‖ := by
  rw [p.fullQuadraticPeriod_eq_actual]
  apply quadraticPeriod_norm_pos hd hα hk (windingTau_pos (d + 1) (by omega))
  rw [show (2 : ℂ) * ((d + 1 : ℕ) : ℂ) =
    ((2 * ((d + 1 : ℕ) : ℝ) : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re]
  have hr := p.curvature_re
  exact div_pos (by linarith) (by positivity)

theorem positiveRadialNormalizer_phase_identity {k : ℕ} (hd : 0 < d)
    (hα : radialShape d = (particleExponent (d + 1) : ℝ))
    (hk : particleExponent (d + 1) < k) :
    p.positiveRadialNormalizer k =
      (‖firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
          (Real.cos φ) (Real.sin φ)‖ /
        (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
          (Real.cos φ) (Real.sin φ)).re) ^ particleExponent (d + 1) *
        ‖p.fullQuadraticPeriod k‖ := by
  let h := firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
    (Real.cos φ) (Real.sin φ)
  let a : ℝ := 2 * ((d + 1 : ℕ) : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hr : 0 < h.re := by have hh := p.curvature_re; dsimp [h]; linarith
  have he : (2 : ℂ) * ((d + 1 : ℕ) : ℂ) = (a : ℂ) := by dsimp [a]; push_cast; rfl
  have hs : 0 < (h / (a : ℂ)).re := by rw [Complex.div_ofReal_re]; exact div_pos hr ha
  have hh := quadraticPeriod_phase_ratio hd hα hk
    (windingTau_pos (d + 1) (by omega)) hs
  have hp : ((h / (a : ℂ)).re : ℂ) = (h.re : ℂ) / (a : ℂ) := by
    rw [Complex.div_ofReal_re, Complex.ofReal_div]
  rw [hp] at hh
  have hnorm : ‖h / (a : ℂ)‖ / (h / (a : ℂ)).re = ‖h‖ / h.re := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le, Complex.div_ofReal_re]
    field_simp
  rw [hnorm] at hh
  have hpos : p.fullPositiveQuadraticPeriod k =
      ∫ v, quadraticPeriodIntegrand d k (windingTau (d + 1))
        ((h.re : ℂ) / (a : ℂ)) v ∂independentMeasure d := by
    unfold fullPositiveQuadraticPeriod
    rw [he]
  have hcomplex : p.fullQuadraticPeriod k =
      ∫ v, quadraticPeriodIntegrand d k (windingTau (d + 1))
        (h / (a : ℂ)) v ∂independentMeasure d := by
    rw [p.fullQuadraticPeriod_eq_actual, he]
  rw [← hpos, ← hcomplex,
    p.norm_fullPositiveQuadraticPeriod hd hk (radialPower_of_integer_shape hα).2] at hh
  exact (div_eq_iff (p.fullQuadraticPeriod_norm_pos hd hα hk).ne').mp hh

theorem positiveRadialNormalizer_phase_bound {k : ℕ} (hd : 0 < d)
    (hα : radialShape d = (particleExponent (d + 1) : ℝ))
    (hk : particleExponent (d + 1) < k) {K : ℝ}
    (hK : ‖B (windingTau (d + 1) : ℂ)‖ ≤ K)
    (hlarge : 2 * curvatureErrorConstant K (Real.cos φ) (Real.sin φ) ≤
      (((d + 1 : ℕ) : ℝ)) ^ 2) :
    p.positiveRadialNormalizer k ≤
      Real.exp (2 * (curvatureErrorConstant K (Real.cos φ) (Real.sin φ)) ^ 2 /
        (((d + 1 : ℕ) : ℝ)) ^ 2) * ‖p.fullQuadraticPeriod k‖ := by
  rw [p.positiveRadialNormalizer_phase_identity hd hα hk]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (firstWindingCurvature_phase_uniform (d + 1) (particleExponent (d + 1))
    (B (windingTau (d + 1) : ℂ)) (Real.cos φ) (Real.sin φ) K
      (by omega) (particleExponent_le_sq _) hK hlarge).2.2

set_option maxHeartbeats 1200000 in
theorem complete_physical_relative_pole_comparison {k : ℕ} (hd : 2 ≤ d)
    (hα : radialShape d = (particleExponent (d + 1) : ℝ))
    (hk : 64 * (d + 1) ^ 2 ≤ k)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKρ : 0 ≤ Kρ) (hKp : 0 ≤ Kp)
    (hKσ : 768 * Kp * σ ≤ 1)
    (hupper : (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)).re ≤ 2)
    (hlarge : 64 * (Kρ * (1 + 2 * Real.pi ^ 2)) ≤ ((d + 1 : ℕ) : ℝ))
    {R δ K : ℝ} (hR : 0 < R) (hRσ : R < σ)
    (hRcentral : 1024 * ((d + 1 : ℕ) : ℝ) / (k : ℝ) < R ^ 2)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hscale : δ ^ 2 = (((d + 1 : ℕ) : ℝ)) ^ 2 / (k : ℝ))
    (hsmall : 2 * (1024 : ℝ) ^ 2 * (Kρ + Kp) * δ ≤ 1 / 32)
    (hK : ‖B (windingTau (d + 1) : ℂ)‖ ≤ K)
    (hphase : 2 * curvatureErrorConstant K (Real.cos φ) (Real.sin φ) ≤
      (((d + 1 : ℕ) : ℝ)) ^ 2) :
    ‖p.compactPoleIntegral k R - p.fullQuadraticPeriod k‖ ≤
      ((angularPerturbationConstant * (2 * (1024 : ℝ) ^ 2 * (Kρ + Kp)) * δ +
        Real.exp (-(((d + 1 : ℕ) : ℝ)) ^ 2 / 4)) *
        Real.exp (2 * (curvatureErrorConstant K (Real.cos φ) (Real.sin φ)) ^ 2 /
          (((d + 1 : ℕ) : ℝ)) ^ 2)) * ‖p.fullQuadraticPeriod k‖ := by
  have hkα : particleExponent (d + 1) < k := by
    have hh := particleExponent_le_sq (d + 1)
    have hNsq : 4 ≤ (d + 1) ^ 2 := by nlinarith
    omega
  have hp := p.complete_physical_pole_period_comparison hd (radialPower_of_integer_shape hα).2
    hk hσ hσ1 hKρ hKp hKσ hupper hlarge hR hRσ hRcentral hδ hδ1 hscale hsmall
  have hcost := p.positiveRadialNormalizer_phase_bound (by omega) hα hkα hK hphase
  have hε : 0 ≤ angularPerturbationConstant * (2 * (1024 : ℝ) ^ 2 * (Kρ + Kp)) * δ +
      Real.exp (-(((d + 1 : ℕ) : ℝ)) ^ 2 / 4) := by
    have hc : 0 ≤ angularPerturbationConstant := angularPerturbationConstant_pos.le
    positivity
  exact hp.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcost hε)

end
end IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
