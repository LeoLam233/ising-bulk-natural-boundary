import IsingBulk.AnisoF002.C03.IsotropicPrimeCoincidence
import IsingBulk.AnisoF002.C03.IsotropicPrimeMeanGap

/-!
# All original integer means avoid the actual prime branch points

No fundamental-interval or selected-lift assumption is needed.  The
reciprocal trace equation identifies both possible exponential roots,
and the actual cyclotomic branch gap excludes every physical constraint.
The lower-particle signed denominators are also specialized to the
literal constrained angular means.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section

theorem reciprocal_trace_eq_roots {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (he : x + x⁻¹ = y + y⁻¹) : x = y ∨ x = y⁻¹ := by
  have hp : x ^ 2 - (y + y⁻¹) * x + 1 = 0 := by
    linear_combination x * he - (mul_inv_cancel₀ hx)
  have hf : (x - y) * (x - y⁻¹) = 0 := by
    linear_combination hp + (mul_inv_cancel₀ hy)
  exact (mul_eq_zero.mp hf).imp sub_eq_zero.mp sub_eq_zero.mp

theorem isotropic_prime_all_constrained_means_nonbranch {p a N : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ha : a.Coprime p) (hN : 0 < N)
    {μ phase : ℝ} (hphase : phase = 0 ∨ phase = Real.pi) (l : ℤ)
    (hmean : (N : ℝ) * μ = 2 * Real.pi * l + phase) :
    |2 * Real.cos (isotropicPrimeAngle p a)| - Real.cos μ ≠ 1 := by
  intro he
  let y := Complex.exp ((μ : ℂ) * Complex.I)
  let r := isotropicPrimeBranchRoot p a
  have hy : y ≠ 0 := Complex.exp_ne_zero _
  have hr : r ≠ 0 := Complex.exp_ne_zero _
  have htrace : y + y⁻¹ = r + r⁻¹ := by
    rw [isotropic_exponential_trace, isotropicPrimeBranchRoot_trace]
    have hc : Real.cos μ = |2 * Real.cos (isotropicPrimeAngle p a)| - 1 := by linarith
    rw [hc]
  have hpow : y ^ N = 1 ∨ y ^ N = -1 := by
    have h := isotropic_exponential_of_integer_mean N μ phase l hmean
    rcases hphase with rfl | rfl
    · left
      simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero] using h
    · right
      simpa only [Complex.exp_pi_mul_I] using h
  have hrpow : r ^ N = 1 ∨ r ^ N = -1 := by
    rcases reciprocal_trace_eq_roots hy hr htrace with hyr | hyr
    · simpa only [hyr] using hpow
    · rw [hyr] at hpow
      rcases hpow with h | h
      · left
        simpa only [inv_pow, inv_inv, inv_one] using congrArg (fun z : ℂ => z⁻¹) h
      · right
        simpa only [inv_pow, inv_inv, inv_neg, inv_one] using congrArg (fun z : ℂ => z⁻¹) h
  exact hrpow.elim (isotropicPrimeBranchRoot_pow_ne_one hp hp5 ha hN)
    (isotropicPrimeBranchRoot_pow_ne_neg_one hp hp5 ha hN)

theorem isotropic_prime_positive_all_means_nonbranch {p a N : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ha : a.Coprime p) (hN : 0 < N)
    (hS : 0 ≤ 2 * Real.cos (isotropicPrimeAngle p a))
    {μ phase : ℝ} (hphase : phase = 0 ∨ phase = Real.pi) (l : ℤ)
    (hmean : (N : ℝ) * μ = 2 * Real.pi * l + phase) :
    2 * Real.cos (isotropicPrimeAngle p a) - Real.cos μ ≠ 1 := by
  simpa only [abs_of_nonneg hS] using
    isotropic_prime_all_constrained_means_nonbranch hp hp5 ha hN hphase l hmean

theorem isotropic_prime_negative_all_means_nonbranch {p a N : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ha : a.Coprime p) (hN : 0 < N)
    (hS : 2 * Real.cos (isotropicPrimeAngle p a) ≤ 0)
    {μ phase : ℝ} (hphase : phase = 0 ∨ phase = Real.pi) (l : ℤ)
    (hmean : (N : ℝ) * μ = 2 * Real.pi * l + phase) :
    2 * Real.cos (Real.pi - isotropicPrimeAngle p a) - Real.cos μ ≠ 1 := by
  have h := isotropic_prime_all_constrained_means_nonbranch hp hp5 ha hN hphase l hmean
  rw [abs_of_nonpos hS] at h
  simpa only [Real.cos_pi_sub, mul_neg, neg_mul] using h

theorem isotropic_positive_lower_mean_denominator {p a N : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ha : a.Coprime p) (hN : 0 < N)
    (hpn : ¬ p ∣ N) (hS : 0 < 2 * Real.cos (isotropicPrimeAngle p a))
    (μ : ℝ) (l : ℤ) (hmean : (N : ℝ) * μ = 2 * Real.pi * l) :
    1 - upperBoundaryRoot (2 * Real.cos (isotropicPrimeAngle p a) - Real.cos μ) ^ N ≠ 0 := by
  apply isotropic_lower_positive_coincidence_denominator hp hp5 hN hpn
    (isotropicPrimeRoot_primitive hp.pos ha) hS (isotropicPrimeRoot_trace p a).symm
  have h := isotropic_exponential_of_integer_mean N μ 0 l (by simpa only [add_zero] using hmean)
  simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero] using h

theorem isotropic_negative_lower_mean_denominator {p a N : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ha : a.Coprime p) (hN : 0 < N) (hodd : Odd N)
    (hpn : ¬ p ∣ N) (hS : 0 < 2 * Real.cos (Real.pi - isotropicPrimeAngle p a))
    (μ : ℝ) (l : ℤ) (hmean : (N : ℝ) * μ = 2 * Real.pi * l + Real.pi) :
    1 - (-1 : ℂ) * upperBoundaryRoot
      (2 * Real.cos (Real.pi - isotropicPrimeAngle p a) - Real.cos μ) ^ N ≠ 0 := by
  apply isotropic_lower_negative_coincidence_denominator hp hp5 hN hodd hpn
    (isotropicPrimeRoot_primitive hp.pos ha) hS
  · rw [isotropicPrimeRoot_trace, Real.cos_pi_sub]
    push_cast
    ring
  · simpa only [Complex.exp_pi_mul_I] using
      isotropic_exponential_of_integer_mean N μ Real.pi l hmean

theorem isotropic_lower_even_not_dvd {p N : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hN : 0 < N) (hlt : N < 2 * p) (heven : Even N) : ¬ p ∣ N := by
  rintro ⟨k, rfl⟩
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hk : k = 1 := by nlinarith [hp.pos]
  rw [hk, mul_one] at heven
  obtain ⟨u, hu⟩ := heven
  obtain ⟨v, hv⟩ := hpodd
  omega

end
end IsingBulk.AnisoF002.Isotropic
