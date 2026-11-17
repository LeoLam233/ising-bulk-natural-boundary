import IsingBulk.AnisoF002.C03.IsotropicPrimeMeanGap
import IsingBulk.AnisoF002.RegularTail.CollisionBudget

/-!
# Exact resonant prime means and the complete higher-particle budget

Both physical first parities and the signed negative HT center satisfy
the literal product resonance. Their integer lifts are supplied exactly.
Every later same-parity particle has enough retained physical pairs for
the already proved complete right-tail bound at the full first order.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open IsingBulk.AnisoF002.RegularTail

theorem isotropic_first_resonance_of_power {N : ℕ} {α : ℝ} {σ : ℂ}
    (hσ : σ ≠ 0) (hpow : Complex.exp ((α : ℂ) * Complex.I) ^ N = σ) :
    σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1 := by
  rw [Complex.exp_neg, Complex.exp_nat_mul, hpow, mul_inv_cancel₀ hσ]

theorem isotropic_prime_odd_first_resonance (p a : ℕ) (hp : 0 < p) :
    (1 : ℂ) * Complex.exp (-((p : ℂ) * ((isotropicPrimeAngle p a : ℂ) * Complex.I))) = 1 :=
  isotropic_first_resonance_of_power one_ne_zero (isotropicPrimeRoot_pow p a hp)

theorem isotropic_prime_even_first_resonance (p a : ℕ) (hp : 0 < p) :
    (1 : ℂ) * Complex.exp (-(((2 * p : ℕ) : ℂ) * ((isotropicPrimeAngle p a : ℂ) * Complex.I))) = 1 := by
  apply isotropic_first_resonance_of_power one_ne_zero
  change isotropicPrimeRoot p a ^ (2 * p) = 1
  rw [Nat.mul_comm 2 p, pow_mul, isotropicPrimeRoot_pow p a hp, one_pow]

theorem isotropic_reflected_prime_root (p a : ℕ) :
    Complex.exp (((Real.pi - isotropicPrimeAngle p a : ℝ) : ℂ) * Complex.I) =
      -(isotropicPrimeRoot p a)⁻¹ := by
  rw [show ((Real.pi - isotropicPrimeAngle p a : ℝ) : ℂ) * Complex.I =
    (Real.pi : ℂ) * Complex.I + -((isotropicPrimeAngle p a : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_neg]
  simp only [neg_one_mul, isotropicPrimeRoot]

theorem isotropic_prime_negative_first_resonance (p a : ℕ) (hp : 0 < p) (hodd : Odd p) :
    (-1 : ℂ) * Complex.exp (-((p : ℂ) *
      (((Real.pi - isotropicPrimeAngle p a : ℝ) : ℂ) * Complex.I))) = 1 := by
  apply isotropic_first_resonance_of_power (neg_ne_zero.mpr one_ne_zero)
  rw [isotropic_reflected_prime_root, neg_pow, hodd.neg_one_pow, inv_pow,
    isotropicPrimeRoot_pow p a hp, inv_one, mul_one]

theorem isotropic_prime_odd_first_mean (p a : ℕ) (b : ℝ) :
    constrainedRightMean p b 0 (-(a : ℤ)) = b - isotropicPrimeAngle p a := by
  simp only [constrainedRightMean, isotropicPrimeAngle, Int.cast_neg, Int.cast_natCast, add_zero]
  ring

theorem isotropic_prime_even_first_mean (p a : ℕ) (hp : 0 < p) (b : ℝ) :
    constrainedRightMean (2 * p) b 0 (-(2 * a : ℤ)) = b - isotropicPrimeAngle p a := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [constrainedRightMean, isotropicPrimeAngle, Int.cast_neg, Int.cast_mul,
    Int.cast_ofNat, Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat, add_zero]
  field_simp
  ring

theorem isotropic_prime_negative_first_mean (d a : ℕ) (b : ℝ) :
    constrainedRightMean (2 * d + 1) b Real.pi ((a : ℤ) - d - 1) =
      b - (Real.pi - isotropicPrimeAngle (2 * d + 1) a) := by
  have hp0 : (2 : ℝ) * d + 1 ≠ 0 := by positivity
  simp only [constrainedRightMean, isotropicPrimeAngle, Int.cast_sub, Int.cast_natCast,
    Int.cast_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  field_simp
  ring

theorem isotropic_all_later_retained_pair_budget {n N j : ℕ}
    (hN : n + 2 ≤ N) (hj : 2 * j ≤ n ^ 2) : j + 1 ≤ N.choose 2 := by
  apply le_trans _ (Nat.choose_le_choose 2 hN)
  rw [Nat.choose_two_right, show n + 2 - 1 = n + 1 by omega]
  have he : (n + 2) * (n + 1) = n ^ 2 + 3 * n + 2 := by ring
  rw [he]
  omega

theorem isotropic_odd_all_later_retained_pair_budget {n N j : ℕ}
    (hN : n + 2 ≤ N) (hj : j ≤ oddTopOrder n) : j + 1 ≤ N.choose 2 :=
  isotropic_all_later_retained_pair_budget hN (odd_derivative_budget hj)

theorem isotropic_even_all_later_retained_pair_budget {n N j : ℕ}
    (hN : n + 2 ≤ N) (hj : j ≤ evenTopOrder n) : j + 1 ≤ N.choose 2 :=
  isotropic_all_later_retained_pair_budget hN (even_derivative_budget hj)

end
end IsingBulk.AnisoF002.Isotropic
