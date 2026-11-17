import IsingBulk.AnisoF002.C03.RegularIsotropicMixedIntegralBounds
import IsingBulk.AnisoF002.C03.IsotropicMixedFactorialTail

/-!
# Summability of the actual integrated mixed-density envelope

The exact physical N! is retained. The protected rho/N^6 disk and the
last constrained one-body factor cost only N^(6j+2); the all-particle
matching envelope controls this for every fixed j and both parities.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail.C03

theorem isotropicParticleNormalization_le_factorial (N : ℕ) :
    ‖isotropicParticleNormalization N‖ ≤ 1 / (N.factorial : ℝ) := by
  have he : ‖isotropicParticleNormalization N‖ =
      1 / ((N.factorial : ℝ) * (2 * Real.pi) ^ (N - 1)) := by
    simp only [isotropicParticleNormalization, norm_inv, norm_mul, norm_pow, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [he]
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < N.factorial)
  have hp : (1 : ℝ) ≤ (2 * Real.pi) ^ (N - 1) := one_le_pow₀ (by linarith [Real.two_le_pi])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N.factorial)

theorem mixedIntegratedEnvelope_nonneg {C g c ρ L : ℝ}
    (hC : 0 ≤ C) (hg : 0 < g) (hc : 0 < c) (hρ : 0 < ρ) (hL : 0 ≤ L) (j N : ℕ) :
    0 ≤ mixedIntegratedEnvelope C g c ρ L j N := by
  have he := mixedDensityEnvelope_nonneg hC hg N
  unfold mixedIntegratedEnvelope
  positivity

theorem mixedIntegratedEnvelope_le_factorial {C g c ρ L : ℝ}
    (hC : 0 ≤ C) (hg : 0 < g) (hc : 0 < c) (hρ : 0 < ρ) (hL : 0 ≤ L)
    (j N : ℕ) :
    mixedIntegratedEnvelope C g c ρ L j N ≤
      (8 * Real.exp 1 * (j.factorial : ℝ) / (g * c * ρ ^ j)) *
        mixedFactorialEnvelope (128 * C * Real.exp 1 * max 1 L) (6 * j + 2) N := by
  by_cases hN : N = 0
  · subst N
    simp only [mixedIntegratedEnvelope, Nat.cast_zero, mul_zero, zero_div, zero_mul]
    unfold mixedFactorialEnvelope
    positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have he : Real.exp ((N : ℝ) / 2) ≤ Real.exp 1 ^ N := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hLp : L ^ (N - 1) ≤ (max 1 L) ^ N :=
    (pow_le_pow_left₀ hL (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le N 1))
  calc
    _ ≤ 2 ^ N * ((j.factorial : ℝ) *
        ((1 / (N.factorial : ℝ)) * ((4 / g) * N) * 4 ^ N *
          (matchingNumber ((N + 1) / 2) : ℝ) * (16 * C) ^ N * Real.exp 1 * Real.exp 1 ^ N) /
        (ρ / (N : ℝ) ^ 6) ^ j) * (2 * N / c) * (max 1 L) ^ N := by
      unfold mixedIntegratedEnvelope mixedDensityEnvelope
      gcongr
      exact isotropicParticleNormalization_le_factorial N
    _ = _ := by
      unfold mixedFactorialEnvelope
      rw [show (128 : ℝ) * C * Real.exp 1 * max 1 L =
        (2 * 4 * (16 * C)) * Real.exp 1 * max 1 L by ring]
      simp only [mul_pow, div_pow, pow_add, ← pow_mul]
      field_simp
      ring

theorem mixedIntegratedEnvelope_summable {C g c ρ L : ℝ}
    (hC : 0 ≤ C) (hg : 0 < g) (hc : 0 < c) (hρ : 0 < ρ) (hL : 0 ≤ L) (j : ℕ) :
    Summable (mixedIntegratedEnvelope C g c ρ L j) := by
  have hA : 0 ≤ 128 * C * Real.exp 1 * max 1 L := by positivity
  have hsum := (mixedFactorialEnvelope_summable hA (6 * j + 2)).mul_left
    (8 * Real.exp 1 * (j.factorial : ℝ) / (g * c * ρ ^ j))
  exact hsum.of_nonneg_of_le (mixedIntegratedEnvelope_nonneg hC hg hc hρ hL j)
    (mixedIntegratedEnvelope_le_factorial hC hg hc hρ hL j)

end
end IsingBulk.AnisoF002.Isotropic
