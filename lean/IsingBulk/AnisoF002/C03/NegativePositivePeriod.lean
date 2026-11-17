import IsingBulk.AnisoF002.C03.NegativePolePeriodComparison

/-!
# The positive radial normalizer is the actual real-curvature period

The beta normalizer in the physical error estimate is identified with a
complete independent-plane integral.  The exact complex period phase
cost therefore applies to that same integral and normalization.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set

theorem quadraticPeriod_as_radial {d α k : ℕ} (hd : 0 < d)
    (hα : radialShape d = (α : ℝ)) (hk : 1 ≤ k) (τ : ℝ) (h : ℂ) :
    (∫ v, quadraticPeriodIntegrand d k τ h v ∂independentMeasure d) =
      (constrainedGaussianIntegral d / Real.Gamma (radialShape d)) •
        complexRadialPeriod α (k - 1) τ h := by
  have hp := (radialPower_of_integer_shape hα).2
  have hh := vandermonde_quadratic_complex_integral hd hp
    (fun q : ℝ => 1 / ((τ : ℂ) + h * q) ^ k)
  simpa only [quadraticPeriodIntegrand, complexRadialPeriod, Complex.real_smul,
    Complex.ofReal_pow, mul_one_div, Nat.sub_add_cancel hk] using hh

theorem quadraticPeriod_norm_pos {d α k : ℕ} (hd : 0 < d)
    (hα : radialShape d = (α : ℝ)) (hk : α < k) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    0 < ‖∫ v, quadraticPeriodIntegrand d k τ h v ∂independentMeasure d‖ := by
  have hα0 := (radialPower_of_integer_shape hα).1
  have hC : 0 < constrainedGaussianIntegral d / Real.Gamma (radialShape d) :=
    div_pos (constrainedGaussianIntegral_pos d) (Real.Gamma_pos_of_pos (radialShape_pos d))
  have hn : 0 < ‖h‖ := hh.trans_le (Complex.re_le_norm h)
  rw [quadraticPeriod_as_radial hd hα (by omega), norm_smul, Real.norm_of_nonneg hC.le,
    norm_complexRadialPeriod α (k - 1) hα0 (by omega) hτ hh]
  positivity

theorem quadraticPeriod_phase_ratio {d α k : ℕ} (hd : 0 < d)
    (hα : radialShape d = (α : ℝ)) (hk : α < k) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    ‖∫ v, quadraticPeriodIntegrand d k τ (h.re : ℂ) v ∂independentMeasure d‖ /
      ‖∫ v, quadraticPeriodIntegrand d k τ h v ∂independentMeasure d‖ = (‖h‖ / h.re) ^ α := by
  have hα0 := (radialPower_of_integer_shape hα).1
  have hC : 0 < constrainedGaussianIntegral d / Real.Gamma (radialShape d) :=
    div_pos (constrainedGaussianIntegral_pos d) (Real.Gamma_pos_of_pos (radialShape_pos d))
  rw [quadraticPeriod_as_radial hd hα (by omega), quadraticPeriod_as_radial hd hα (by omega),
    norm_smul, norm_smul, Real.norm_of_nonneg hC.le]
  calc
    _ = ‖complexRadialPeriod α (k - 1) τ (h.re : ℂ)‖ /
        ‖complexRadialPeriod α (k - 1) τ h‖ := by
      rw [mul_div_mul_left _ _ hC.ne']
    _ = _ := radialPeriod_majorant_ratio α (k - 1) hα0 (by omega) hτ hh

end
end IsingBulk.AnisoF002.NegativeHT.Angular

namespace IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
noncomputable section
open MeasureTheory Set Angular

variable {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {d : ℕ}
variable (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)

def fullPositiveQuadraticPeriod (_p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)
    (k : ℕ) : ℂ :=
  ∫ v, quadraticPeriodIntegrand d k (windingTau (d + 1))
    (((firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)).re : ℂ) / (2 * ((d + 1 : ℕ) : ℂ))) v ∂independentMeasure d

theorem positiveRadialNormalizer_pos {k : ℕ} (hd : 0 < d)
    (hk : particleExponent (d + 1) < k) : 0 < p.positiveRadialNormalizer k := by
  have hα : 0 < particleExponent (d + 1) := by
    have hs : 4 ≤ (d + 1) ^ 2 := by nlinarith
    unfold particleExponent
    omega
  exact mul_pos (div_pos p.poleRadialScaleFactor_pos
    (pow_pos (windingTau_pos (d + 1) (by omega)) _))
      (radialBeta_pos (particleExponent (d + 1)) (k - 1) hα (by omega))

set_option maxHeartbeats 1200000 in
theorem fullPositiveQuadraticPeriod_eq_normalizer (k : ℕ) (hd : 0 < d) (hk : 1 ≤ k)
    (ha : radialPower d = 2 * (particleExponent (d + 1) - 1) + 1) :
    p.fullPositiveQuadraticPeriod k = (p.positiveRadialNormalizer k : ℂ) := by
  let τ := windingTau (d + 1)
  let a := (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
    (Real.cos φ) (Real.sin φ)).re
  have ha0 : 0 < a := by have hh := p.curvature_re; dsimp [a]; linarith
  have hτ : 0 < τ := windingTau_pos (d + 1) (by omega)
  have hN : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  have hα : 0 < particleExponent (d + 1) := by
    have hs : 4 ≤ (d + 1) ^ 2 := by nlinarith
    unfold particleExponent
    omega
  let f : ℝ → ℂ := fun q => 1 / ((τ : ℂ) + (a : ℂ) /
    (2 * ((d + 1 : ℕ) : ℂ)) * q) ^ k
  have hh := vandermonde_quadratic_complex_integral hd ha f
  have hl : (fun v : constrainedPlane d => planeVandermonde v • f (‖v‖ ^ 2)) =
      quadraticPeriodIntegrand d k τ ((a : ℂ) / (2 * ((d + 1 : ℕ) : ℂ))) := by
    funext v
    simp only [f, quadraticPeriodIntegrand, Complex.real_smul, mul_one_div]
  rw [hl, radial_power_scale (particleExponent (d + 1) - 1) p.radialScale_pos f,
    smul_smul, Nat.sub_add_cancel hα] at hh
  change p.fullPositiveQuadraticPeriod k = p.poleRadialScaleFactor •
    ∫ x in Ioi (0 : ℝ), x ^ (particleExponent (d + 1) - 1) • f (p.radialScale * x) at hh
  have hden (x : ℝ) : (τ : ℂ) + (a : ℂ) / (2 * ((d + 1 : ℕ) : ℂ)) *
      (p.radialScale * x : ℝ) = (τ : ℂ) * ((1 + x : ℝ) : ℂ) := by
    unfold radialScale
    change (τ : ℂ) + (a : ℂ) / (2 * ((d + 1 : ℕ) : ℂ)) *
      ((2 * ((d + 1 : ℕ) : ℝ) * τ / a * x : ℝ) : ℂ) = _
    push_cast
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    have hNC : (((d + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have hf : (fun x : ℝ => x ^ (particleExponent (d + 1) - 1) • f (p.radialScale * x)) =
      (fun x => ((τ : ℂ) ^ k)⁻¹ * (radialBetaDensity (particleExponent (d + 1)) (k - 1) x : ℂ)) := by
    funext x
    dsimp only [f, radialBetaDensity]
    rw [hden x, mul_pow, Complex.real_smul, Nat.sub_add_cancel hk]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hh, hf, integral_const_mul, integral_complex_ofReal]
  change p.poleRadialScaleFactor • (((τ : ℂ) ^ k)⁻¹ *
    (radialBeta (particleExponent (d + 1)) (k - 1) : ℂ)) = _
  dsimp only [positiveRadialNormalizer, τ]
  rw [Complex.real_smul]
  push_cast
  ring

theorem norm_fullPositiveQuadraticPeriod {k : ℕ} (hd : 0 < d)
    (hk : particleExponent (d + 1) < k)
    (ha : radialPower d = 2 * (particleExponent (d + 1) - 1) + 1) :
    ‖p.fullPositiveQuadraticPeriod k‖ = p.positiveRadialNormalizer k := by
  rw [p.fullPositiveQuadraticPeriod_eq_normalizer k hd (by omega) ha,
    Complex.norm_real, Real.norm_of_nonneg (p.positiveRadialNormalizer_pos hd hk).le]

end
end IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
