import IsingBulk.AnisoF002.C03.RegularModelAnalyticFactors

/-!
# Exact logarithmic decomposition of the genuine first-winding model

Every factor of M(n,j) is retained.  The logarithmic correction to the
temperature is identified with the literal normalized sinc expression;
the gamma correction is the already checked finite sum.  The remaining
analytic factors are organized for finite differences, not replaced by
a pointwise asymptotic estimate.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

theorem complexSinc_ofReal (x : ℝ) : complexSinc (x : ℂ) = (Real.sinc x : ℂ) := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    rw [complexSinc, dslope_of_ne _ hxC, slope, Real.sinc_of_ne_zero hx]
    simp only [vsub_eq_sub, sub_zero, Complex.sin_zero, smul_eq_mul, div_eq_mul_inv,
      Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sin, mul_comm]

theorem inverseParticleLogTemperature_reciprocal_re (n : ℕ) (hn : 0 < n) :
    (inverseParticleLogTemperature (n : ℂ)⁻¹).re =
      Real.log (windingTau n) + 2 * Real.log (n : ℝ) - Real.log (Real.pi ^ 2 / 2) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hA : 0 < Real.pi ^ 2 / 2 := by positivity
  have hτ := windingTau_pos n hn
  have h := congrArg Real.log (windingTau_normalized_sinc n hn)
  rw [Real.log_div (mul_ne_zero hτ.ne' (pow_ne_zero 2 hnR.ne')) hA.ne',
    Real.log_mul hτ.ne' (pow_ne_zero 2 hnR.ne'), Real.log_pow, Real.log_pow] at h
  have hx : (Real.pi : ℂ) * (n : ℂ)⁻¹ / 2 = (Real.pi / (2 * (n : ℝ)) : ℝ) := by
    push_cast
    ring
  rw [inverseParticleLogTemperature, hx, complexSinc_ofReal]
  norm_num only [Complex.mul_re, Complex.log_ofReal_re, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero]
  linarith

theorem particleExponent_real_odd {n : ℕ} (hn : Odd n) :
    (particleExponent n : ℝ) = ((n : ℝ) ^ 2 - 1) / 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [particleExponent_odd]
  push_cast
  ring

theorem log_modelMagnitude_factors (n j : ℕ) (B h s τ : ℝ)
    (hn : 0 < n) (hB : 0 < B) (hh : 0 < h) (hs : 0 < s) (hτ : 0 < τ)
    (hj : 0 < j) (ha : particleExponent n ≤ j) :
    Real.log (modelMagnitude n j B h s τ) =
      Real.log (factorialProduct n) + ((particleExponent n : ℝ) - 3 / 2) * Real.log n +
      (2 - (particleExponent n : ℝ)) * Real.log 2 +
      ((particleExponent n : ℝ) - 1 / 2) * Real.log B -
      ((n : ℝ) - 1) / 2 * Real.log Real.pi -
      (2 * (particleExponent n : ℝ)) * Real.log s - (particleExponent n : ℝ) * Real.log h +
      ((particleExponent n : ℝ) - (j : ℝ) - 1) * Real.log τ -
      (particleExponent n : ℝ) * Real.log j + logGammaCorrection (j : ℝ) (particleExponent n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp := factorialProduct_pos n
  have hg := gammaQuotient_pos j (particleExponent n)
  unfold modelMagnitude modelPrefactor
  repeat' first
    | rw [Real.log_mul (by positivity) (by positivity)]
    | rw [Real.log_div (by positivity) (by positivity)]
    | rw [Real.log_rpow (by positivity)]
    | rw [Real.log_pow]
  rw [log_gammaQuotient_exact j _ hj ha]
  push_cast
  ring

def actualModelLog (B : ℂ → ℂ) (c s : ℝ) (n j : ℕ) : ℝ :=
  Real.log ‖modelCoefficient n j (B (windingTau n : ℂ))
    (firstWindingCurvature n (B (windingTau n : ℂ)) c s) s (windingTau n)‖

def actualModelRemainder (B : ℂ → ℂ) (c s : ℝ) (n : ℕ) : ℝ :=
  (2 - (particleExponent n : ℝ)) * Real.log 2 +
    ((particleExponent n : ℝ) - 1 / 2) * (inverseParticleLogB B (n : ℂ)⁻¹).re -
    ((n : ℝ) - 1) / 2 * Real.log Real.pi -
    2 * (particleExponent n : ℝ) * Real.log s -
    (particleExponent n : ℝ) * (inverseParticleLogCurvature B c s (n : ℂ)⁻¹).re +
    ((particleExponent n : ℝ) - 1) * Real.log (Real.pi ^ 2 / 2) +
    ((particleExponent n : ℝ) - 1) * (inverseParticleLogTemperature (n : ℂ)⁻¹).re

theorem actualModelLog_exact_decomposition {B : ℂ → ℂ} (c s : ℝ) (n j : ℕ)
    (hn : Odd n) (hB : B (windingTau n : ℂ) ≠ 0)
    (hh : firstWindingCurvature n (B (windingTau n : ℂ)) c s ≠ 0)
    (hs : 0 < s) (hj : 0 < j) (ha : particleExponent n ≤ j) :
    actualModelLog B c s n j =
      Real.log (factorialProduct n) + (2 * (j : ℝ) - (n : ℝ) ^ 2 / 2 + 1) * Real.log n -
      (particleExponent n : ℝ) * Real.log j - (j : ℝ) * Real.log (Real.pi ^ 2 / 2) +
      actualModelRemainder B c s n - (j : ℝ) * (inverseParticleLogTemperature (n : ℂ)⁻¹).re +
      logGammaCorrection (j : ℝ) (particleExponent n) := by
  rw [actualModelLog, norm_modelCoefficient _ _ _ _ _ _ hn.pos hs (windingTau_pos n hn.pos),
    log_modelMagnitude_factors _ _ _ _ _ _ hn.pos (norm_pos_iff.mpr hB)
      (norm_pos_iff.mpr hh) hs (windingTau_pos n hn.pos) hj ha]
  have he := inverseParticleLogTemperature_reciprocal_re n hn.pos
  have hb : (inverseParticleLogB B (n : ℂ)⁻¹).re = Real.log ‖B (windingTau n : ℂ)‖ := by
    rw [inverseParticleLogB, inverseParticleTemperature_reciprocal, Complex.log_re]
  have hh' : (inverseParticleLogCurvature B c s (n : ℂ)⁻¹).re =
      Real.log ‖firstWindingCurvature n (B (windingTau n : ℂ)) c s‖ := by
    rw [inverseParticleLogCurvature, inverseParticleCurvature_reciprocal, Complex.log_re]
  unfold actualModelRemainder
  rw [hb, hh', particleExponent_real_odd hn] at *
  linear_combination -(((n : ℝ) ^ 2 - 1) / 2 - (j : ℝ) - 1) * he

theorem actualModelRemainder_analytic_form {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0)
    (hslit : B 0 ∈ Complex.slitPlane) (c s : ℝ) :
    ∃ q₂ q₁ q₀ : ℝ, ∃ U : ℂ → ℂ, AnalyticAt ℂ U 0 ∧ (∀ x, U (-x) = U x) ∧
      ∀ n : ℕ, Odd n →
        actualModelRemainder B c s n = q₂ * (n : ℝ) ^ 2 + q₁ * (n : ℝ) + q₀ +
          (U (n : ℂ)⁻¹).re := by
  obtain ⟨U, V, E, hU, hV, hE, heven, hb, hh, he⟩ := actual_model_logarithm_fills hB hslit c s
  let R : ℂ → ℂ := fun x => (1 / 2 - x ^ 2) * U x -
    (1 / 2 - x ^ 2 / 2) * V x + (1 / 2 - 3 * x ^ 2 / 2) * E x
  have hR : AnalyticAt ℂ R 0 :=
    (((analyticAt_const.sub (analyticAt_id.pow 2)).mul hU).sub
      ((analyticAt_const.sub ((analyticAt_id.pow 2).div_const)).mul hV)).add
        ((analyticAt_const.sub ((analyticAt_const.mul (analyticAt_id.pow 2)).div_const)).mul hE)
  refine ⟨(-Real.log 2 + Real.log ‖B 0‖ - 2 * Real.log s + Real.log (Real.pi ^ 2 / 2)) / 2,
    -Real.log Real.pi / 2,
    5 / 2 * Real.log 2 - Real.log ‖B 0‖ + Real.log Real.pi / 2 + Real.log s -
      3 / 2 * Real.log (Real.pi ^ 2 / 2), R, hR, ?_, ?_⟩
  · intro x
    simp only [R, neg_sq, (heven x).1, (heven x).2.1, (heven x).2.2]
  · intro n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.pos.ne'
    unfold actualModelRemainder
    rw [hb, hh, he, particleExponent_real_odd hn]
    have hcast : (n : ℂ)⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by simp
    rw [hcast]
    dsimp only [R]
    norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, pow_two,
      Complex.log_re, Complex.div_re, Complex.div_im, Complex.normSq_apply]
    field_simp [hnR]
    ring

end
end IsingBulk.AnisoF002.NegativeHT
