import IsingBulk.AnisoF002.C03.IsotropicPrimeAllMeans
import IsingBulk.AnisoF002.C03.IsotropicFirstPrimeResonance

/-!
# Every other actual mean of the first particle is nonresonant

The full first-prime cyclotomic uniqueness theorem is used on the
literal boundary product denominator, for both parities and both HT
determinant signs. Only the two physical coincidence centers survive.
The actual lower partition treats the negative center and vanishes
near its positive reflection.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set

theorem isotropic_prime_first_odd_other_mean {p a : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (ha : a.Coprime p)
    (hα : isotropicPrimeAngle p a ∈ Icc 0 Real.pi)
    (hS : 0 < 2 * Real.cos (isotropicPrimeAngle p a))
    {μ : ℝ} (hμ : μ ∈ Icc (-Real.pi) Real.pi) (l : ℤ)
    (hmean : (p : ℝ) * μ = 2 * Real.pi * l)
    (hnep : μ ≠ isotropicPrimeAngle p a) (hnem : μ ≠ -isotropicPrimeAngle p a) :
    1 - upperBoundaryRoot (2 * Real.cos (isotropicPrimeAngle p a) - Real.cos μ) ^ p ≠ 0 := by
  intro hz
  have hconstraint : Complex.exp ((μ : ℂ) * Complex.I) ^ p = 1 := by
    simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero] using
      isotropic_exponential_of_integer_mean p μ 0 l (by simpa only [add_zero] using hmean)
  have hcos := isotropic_first_odd_coincidence_cos hp hp7 (isotropicPrimeRoot_primitive hp.pos ha)
    hS (isotropicPrimeRoot_trace p a).symm hconstraint hz
  have hcos' : Real.cos μ = Real.cos (isotropicPrimeAngle p a) := by linarith
  exact (isotropic_cosine_pair_centers hα hμ hcos').elim hnep hnem

theorem isotropic_prime_first_even_other_mean {p a : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (ha : a.Coprime p)
    (hα : isotropicPrimeAngle p a ∈ Icc 0 Real.pi)
    (hS : 0 < 2 * Real.cos (isotropicPrimeAngle p a))
    {μ : ℝ} (hμ : μ ∈ Icc (-Real.pi) Real.pi) (l : ℤ)
    (hmean : ((2 * p : ℕ) : ℝ) * μ = 2 * Real.pi * l)
    (hnep : μ ≠ isotropicPrimeAngle p a) (hnem : μ ≠ -isotropicPrimeAngle p a) :
    1 - upperBoundaryRoot (2 * Real.cos (isotropicPrimeAngle p a) - Real.cos μ) ^ (2 * p) ≠ 0 := by
  intro hz
  have hconstraint : Complex.exp ((μ : ℂ) * Complex.I) ^ (2 * p) = 1 := by
    simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero] using
      isotropic_exponential_of_integer_mean (2 * p) μ 0 l (by simpa only [add_zero] using hmean)
  have hcos := isotropic_first_even_coincidence_cos hp hp7 (isotropicPrimeRoot_primitive hp.pos ha)
    hS (isotropicPrimeRoot_trace p a).symm hconstraint hz
  have hcos' : Real.cos μ = Real.cos (isotropicPrimeAngle p a) := by linarith
  exact (isotropic_cosine_pair_centers hα hμ hcos').elim hnep hnem

theorem isotropic_prime_first_negative_other_mean {p a : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (ha : a.Coprime p)
    (hα : Real.pi - isotropicPrimeAngle p a ∈ Icc 0 Real.pi)
    (hS : 0 < 2 * Real.cos (Real.pi - isotropicPrimeAngle p a))
    {μ : ℝ} (hμ : μ ∈ Icc (-Real.pi) Real.pi) (l : ℤ)
    (hmean : (p : ℝ) * μ = 2 * Real.pi * l + Real.pi)
    (hnep : μ ≠ Real.pi - isotropicPrimeAngle p a)
    (hnem : μ ≠ -(Real.pi - isotropicPrimeAngle p a)) :
    1 - (-1 : ℂ) * upperBoundaryRoot
      (2 * Real.cos (Real.pi - isotropicPrimeAngle p a) - Real.cos μ) ^ p ≠ 0 := by
  intro hz
  have hconstraint : Complex.exp ((μ : ℂ) * Complex.I) ^ p = -1 := by
    simpa only [Complex.exp_pi_mul_I] using
      isotropic_exponential_of_integer_mean p μ Real.pi l hmean
  have hpoint : (2 * Real.cos (Real.pi - isotropicPrimeAngle p a) : ℝ) =
      -(isotropicPrimeRoot p a + (isotropicPrimeRoot p a)⁻¹) := by
    rw [isotropicPrimeRoot_trace, Real.cos_pi_sub]
    push_cast
    ring
  have hcos := isotropic_first_negative_coincidence_cos hp hp7 (isotropicPrimeRoot_primitive hp.pos ha)
    hS hpoint hconstraint hz
  have hcos' : Real.cos μ = Real.cos (Real.pi - isotropicPrimeAngle p a) := by linarith
  exact (isotropic_cosine_pair_centers hα hμ hcos').elim hnep hnem

theorem isotropic_constrained_mean_injective {N : ℕ} (hN : 0 < N)
    (phase : ℝ) : Function.Injective (fun l : ℤ => (2 * Real.pi * (l : ℝ) + phase) / N) := by
  intro l k he
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hh := (div_left_inj' hN0).mp he
  have hp : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have heq : (l : ℝ) = (k : ℝ) := mul_left_cancel₀ hp (add_right_cancel hh)
  exact_mod_cast heq

end
end IsingBulk.AnisoF002.Isotropic
