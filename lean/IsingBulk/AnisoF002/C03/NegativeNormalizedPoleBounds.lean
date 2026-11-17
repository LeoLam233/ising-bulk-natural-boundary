import IsingBulk.AnisoF002.C03.NegativeNormalizedPole
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Central and tail bounds for the literal normalized compact pole error -/

namespace IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
noncomputable section
open MeasureTheory Set Angular

variable {b B : ℂ → ℂ} {φ σ C Kρ Kp : ℝ} {d : ℕ}
variable (p : PhysicalFirstWindingData b B φ (d + 1) σ C Kρ Kp)

theorem radialRadius_central_bound {k : ℕ} (hk : 0 < k)
    (hupper : (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)).re ≤ 2)
    {x : ℝ} (hx : 0 ≤ x) (hcut : x ≤ 32 * (((d + 1 : ℕ) : ℝ)) ^ 2 / (k : ℝ)) :
    p.radialRadius x ^ 2 ≤ 1024 * ((d + 1 : ℕ) : ℝ) / (k : ℝ) := by
  have hN : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  obtain ⟨_, _, hu⟩ := radial_parameter_comparison hN
    (windingTau_pos (d + 1) (by omega)) (sq_nonneg (p.radialRadius x))
    (windingTau_bounds (d + 1) (by omega)).1
    (windingTau_bounds (d + 1) (by omega)).2 p.curvature_re hupper
  rw [p.radialRadius_parameter hx] at hu
  have hpi : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hux : ((d + 1 : ℕ) : ℝ) * p.radialRadius x ^ 2 ≤ 32 * x :=
    hu.trans (by nlinarith)
  have hcut' := (le_div_iff₀ hkR).mp hcut
  have hh := mul_le_mul_of_nonneg_right hux hkR.le
  have ht : ((d + 1 : ℕ) : ℝ) * (p.radialRadius x ^ 2 * (k : ℝ)) ≤
      ((d + 1 : ℕ) : ℝ) * (1024 * ((d + 1 : ℕ) : ℝ)) := by nlinarith
  exact (le_div_iff₀ hkR).mpr ((mul_le_mul_iff_right₀ hN).mp ht)

theorem radialRadius_outer_bound {k : ℕ} (hk : 0 < k)
    (hupper : (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)).re ≤ 2)
    {x : ℝ} (hx : 0 ≤ x) (hcut : 32 * (((d + 1 : ℕ) : ℝ)) ^ 2 / (k : ℝ) < x) :
    32 * ((d + 1 : ℕ) : ℝ) / (k : ℝ) ≤ p.radialRadius x ^ 2 := by
  have hN : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  obtain ⟨_, hu, _⟩ := radial_parameter_comparison hN
    (windingTau_pos (d + 1) (by omega)) (sq_nonneg (p.radialRadius x))
    (windingTau_bounds (d + 1) (by omega)).1
    (windingTau_bounds (d + 1) (by omega)).2 p.curvature_re hupper
  rw [p.radialRadius_parameter hx] at hu
  have hcut' := (div_lt_iff₀ hkR).mp hcut
  have hh := mul_le_mul_of_nonneg_right hu hkR.le
  have ht : ((d + 1 : ℕ) : ℝ) * (32 * ((d + 1 : ℕ) : ℝ)) ≤
      ((d + 1 : ℕ) : ℝ) * (p.radialRadius x ^ 2 * (k : ℝ)) := by nlinarith
  exact (div_le_iff₀ hkR).mpr ((mul_le_mul_iff_right₀ hN).mp ht)

theorem normalize_denominator_bound {k : ℕ} {x ε : ℝ} {z : ℂ}
    (hx : 0 ≤ x)
    (hb : ‖z‖ ≤ ε /
      (windingTau (d + 1) +
        (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
          (Real.cos φ) (Real.sin φ)).re * p.radialRadius x ^ 2 /
            (2 * ((d + 1 : ℕ) : ℝ))) ^ k) :
    ‖(windingTau (d + 1) : ℂ) ^ k * z‖ ≤ ε / (1 + x) ^ k := by
  have ht := windingTau_pos (d + 1) (by omega)
  rw [p.radialRadius_denominator hx, mul_pow] at hb
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le]
  calc
    _ ≤ windingTau (d + 1) ^ k *
        (ε / (windingTau (d + 1) ^ k * (1 + x) ^ k)) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg ht.le _)
    _ = _ := by field_simp

theorem normalizedPoleError_central {k : ℕ} (hd : 2 ≤ d) (hk : 0 < k)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKρ : 0 ≤ Kρ) (hKp : 0 ≤ Kp)
    (hKσ : 48 * Kp * σ ≤ 1)
    (hupper : (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)).re ≤ 2)
    {R δ : ℝ} (hR : 0 < R) (hRσ : R < σ)
    (hRcentral : 1024 * ((d + 1 : ℕ) : ℝ) / (k : ℝ) < R ^ 2)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hscale : δ ^ 2 = (((d + 1 : ℕ) : ℝ)) ^ 2 / (k : ℝ))
    (hsmall : 2 * (1024 : ℝ) ^ 2 * (Kρ + Kp) * δ ≤ 1 / 32)
    {x : ℝ} (hx : 0 < x) (hcut : x ≤ 32 * (((d + 1 : ℕ) : ℝ)) ^ 2 / (k : ℝ)) :
    ‖p.normalizedPoleError k R x‖ ≤
      (angularPerturbationConstant * (2 * (1024 : ℝ) ^ 2 * (Kρ + Kp)) * δ) /
        (1 + x) ^ k := by
  have hr := p.radialRadius_nonneg x
  have hcentral := p.radialRadius_central_bound hk hupper hx.le hcut
  have hrR : p.radialRadius x < R := by nlinarith
  have hh := p.central_angularPoleMean_comparison hd hk hσ hσ1 hKρ hKp hKσ
    hr (hrR.trans hRσ) (by norm_num : (1 : ℝ) ≤ 1024) hδ hδ1 hscale hcentral hsmall
  unfold normalizedPoleError
  rw [p.compactAngularMean_inside k hr hrR.le]
  exact p.normalize_denominator_bound hx.le hh

theorem normalized_quadratic_bound (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ‖(windingTau (d + 1) : ℂ) ^ k *
      (1 / angularQuadraticPole d (windingTau (d + 1))
        (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
          (Real.cos φ) (Real.sin φ)) (p.radialRadius x) ^ k)‖ ≤
      1 / (1 + x) ^ k := by
  apply p.normalize_denominator_bound hx
  rw [norm_div, norm_one, norm_pow]
  have ht := windingTau_pos (d + 1) (by omega)
  have hh := p.curvature_re
  apply div_le_div_of_nonneg_left zero_le_one (pow_pos (by positivity) _)
  apply pow_le_pow_left₀ (by positivity)
  have he := Complex.re_le_norm (angularQuadraticPole d (windingTau (d + 1))
    (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)) (p.radialRadius x))
  simpa only [angularQuadraticPole, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, mul_zero, sub_zero, mul_div_assoc] using he

theorem normalizedPoleError_tail {k : ℕ} (hd : 0 < d) (hk8 : 8 ≤ k)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hKρ : 0 ≤ Kρ) (hKp : 0 ≤ Kp)
    (hKσ : 768 * Kp * σ ≤ 1)
    (hupper : (firstWindingCurvature (d + 1) (B (windingTau (d + 1) : ℂ))
      (Real.cos φ) (Real.sin φ)).re ≤ 2)
    (hlarge : 64 * (Kρ * (1 + 2 * Real.pi ^ 2)) ≤ ((d + 1 : ℕ) : ℝ))
    (hk : (((d + 1 : ℕ) : ℝ)) ^ 2 ≤ (k : ℝ))
    {R : ℝ} (hRσ : R < σ) {x : ℝ}
    (hcut : 32 * (((d + 1 : ℕ) : ℝ)) ^ 2 / (k : ℝ) < x) :
    ‖p.normalizedPoleError k R x‖ ≤ 1 / (1 + x) ^ (k / 2 + k / 4 + 1) := by
  have hx : 0 ≤ x := (by positivity : 0 ≤ 32 * (((d + 1 : ℕ) : ℝ)) ^ 2 / (k : ℝ)).trans hcut.le
  have hr := p.radialRadius_nonneg x
  have ht := windingTau_pos (d + 1) (by omega)
  unfold normalizedPoleError
  by_cases hinside : p.radialRadius x ≤ R
  · rw [p.compactAngularMean_inside k hr hinside]
    have hA : 2 * Real.pi ^ 2 ≤ 32 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
    have hh := p.outer_angularPoleMean_comparison hd hk8 hσ hσ1 hKρ hKp hKσ hupper hlarge hk
      hr (hinside.trans_lt hRσ) hA (p.radialRadius_outer_bound (by omega) hupper hx hcut)
    dsimp only at hh
    rw [p.radialRadius_parameter hx] at hh
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le]
    calc
      _ ≤ windingTau (d + 1) ^ k *
          (1 / (windingTau (d + 1) ^ k * (1 + x) ^ (k / 2 + k / 4 + 1))) :=
        mul_le_mul_of_nonneg_left hh (pow_nonneg ht.le _)
      _ = _ := by field_simp
  · rw [p.compactAngularMean_outside k hr (lt_of_not_ge hinside), zero_sub, mul_neg, norm_neg]
    apply (p.normalized_quadratic_bound k hx).trans
    apply div_le_div_of_nonneg_left zero_le_one (by positivity)
    exact pow_le_pow_right₀ (by linarith : 1 ≤ 1 + x) (by omega : k / 2 + k / 4 + 1 ≤ k)

end
end IsingBulk.AnisoF002.NegativeHT.PhysicalFirstWindingData
