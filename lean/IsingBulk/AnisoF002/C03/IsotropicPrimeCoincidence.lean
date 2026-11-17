import IsingBulk.AnisoF002.C03.IsotropicFirstPrimeArithmetic
import IsingBulk.AnisoF002.C03.IsotropicPrimeBranchGap
import IsingBulk.AnisoF002.C03.IsotropicBoundaryRoot

/-!
# Actual boundary denominators at isotropic coincidences

The cyclotomic first-order argument is attached to the actual upper
boundary root, including its branch and off-arc values. No selected
normal form is substituted for the original product denominator.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section

theorem upperBoundaryRoot_trace (w : ℝ) (hw : -1 < w) :
    upperBoundaryRoot w + (upperBoundaryRoot w)⁻¹ = 2 * (w : ℂ) := by
  have h0 := upperBoundaryRoot_ne_zero w hw
  have hp := (upperBoundaryRoot_spec w hw).1
  apply (mul_right_cancel₀ h0)
  rw [add_mul, inv_mul_cancel₀ h0]
  linear_combination hp

theorem isotropic_boundary_coincidence_trace (S θ : ℝ) (hS : 0 < S) :
    (Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) +
      (upperBoundaryRoot (S - Real.cos θ) + (upperBoundaryRoot (S - Real.cos θ))⁻¹) =
        2 * (S : ℂ) := by
  rw [isotropic_exponential_trace, upperBoundaryRoot_trace _
    (by linarith [Real.cos_le_one θ] : -1 < S - Real.cos θ)]
  push_cast
  ring

theorem isotropic_lower_positive_coincidence_denominator {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hpn : ¬ p ∣ n)
    {x : ℂ} (hx : IsPrimitiveRoot x p) {S θ : ℝ} (hS : 0 < S)
    (hpoint : (S : ℂ) = x + x⁻¹)
    (hconstraint : Complex.exp ((θ : ℂ) * Complex.I) ^ n = 1) :
    1 - upperBoundaryRoot (S - Real.cos θ) ^ n ≠ 0 := by
  intro he
  have hr : upperBoundaryRoot (S - Real.cos θ) ^ n = 1 := (sub_eq_zero.mp he).symm
  apply isotropic_prime_trace_not_competitors hp hp5 hn hpn hx hconstraint hr
  rw [← hpoint]
  exact (isotropic_boundary_coincidence_trace S θ hS).symm

theorem isotropic_lower_negative_coincidence_denominator {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hodd : Odd n) (hpn : ¬ p ∣ n)
    {x : ℂ} (hx : IsPrimitiveRoot x p) {S θ : ℝ} (hS : 0 < S)
    (hpoint : (S : ℂ) = -(x + x⁻¹))
    (hconstraint : Complex.exp ((θ : ℂ) * Complex.I) ^ n = -1) :
    1 - (-1 : ℂ) * upperBoundaryRoot (S - Real.cos θ) ^ n ≠ 0 := by
  intro he
  have hr : upperBoundaryRoot (S - Real.cos θ) ^ n = -1 := by linear_combination he
  apply isotropic_negative_prime_trace_not_competitors hp hp5 hn hodd hpn hx hconstraint hr
  rw [← hpoint]
  exact (isotropic_boundary_coincidence_trace S θ hS).symm

theorem isotropic_first_odd_coincidence_cos {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {x : ℂ} (hx : IsPrimitiveRoot x p) {S θ : ℝ} (hS : 0 < S)
    (hpoint : (S : ℂ) = x + x⁻¹)
    (hconstraint : Complex.exp ((θ : ℂ) * Complex.I) ^ p = 1)
    (hdenom : 1 - upperBoundaryRoot (S - Real.cos θ) ^ p = 0) :
    Real.cos θ = S / 2 := by
  have hr := (sub_eq_zero.mp hdenom).symm
  have he : 2 * (x + x⁻¹) =
      (Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) +
      (upperBoundaryRoot (S - Real.cos θ) + (upperBoundaryRoot (S - Real.cos θ))⁻¹) := by
    rw [← hpoint]
    exact (isotropic_boundary_coincidence_trace S θ hS).symm
  have hpair := (isotropic_prime_trace_unique hp hp7 hx hconstraint hr he).1
  rw [isotropic_exponential_trace, ← hpoint] at hpair
  have hre := congrArg Complex.re hpair
  simp only [Complex.ofReal_re] at hre
  linarith

theorem isotropic_first_even_coincidence_cos {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {x : ℂ} (hx : IsPrimitiveRoot x p) {S θ : ℝ} (hS : 0 < S)
    (hpoint : (S : ℂ) = x + x⁻¹)
    (hconstraint : Complex.exp ((θ : ℂ) * Complex.I) ^ (2 * p) = 1)
    (hdenom : 1 - upperBoundaryRoot (S - Real.cos θ) ^ (2 * p) = 0) :
    Real.cos θ = S / 2 := by
  have hr := (sub_eq_zero.mp hdenom).symm
  have he : 2 * (x + x⁻¹) =
      (Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) +
      (upperBoundaryRoot (S - Real.cos θ) + (upperBoundaryRoot (S - Real.cos θ))⁻¹) := by
    rw [← hpoint]
    exact (isotropic_boundary_coincidence_trace S θ hS).symm
  have hpair := (isotropic_twice_prime_trace_unique hp hp7 hx hconstraint hr he).1
  rw [isotropic_exponential_trace, ← hpoint] at hpair
  have hre := congrArg Complex.re hpair
  simp only [Complex.ofReal_re] at hre
  linarith

theorem isotropic_first_negative_coincidence_cos {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {x : ℂ} (hx : IsPrimitiveRoot x p) {S θ : ℝ} (hS : 0 < S)
    (hpoint : (S : ℂ) = -(x + x⁻¹))
    (hconstraint : Complex.exp ((θ : ℂ) * Complex.I) ^ p = -1)
    (hdenom : 1 - (-1 : ℂ) * upperBoundaryRoot (S - Real.cos θ) ^ p = 0) :
    Real.cos θ = S / 2 := by
  have hr : upperBoundaryRoot (S - Real.cos θ) ^ p = -1 := by linear_combination hdenom
  have he : 2 * (-(x + x⁻¹)) =
      (Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹) +
      (upperBoundaryRoot (S - Real.cos θ) + (upperBoundaryRoot (S - Real.cos θ))⁻¹) := by
    rw [← hpoint]
    exact (isotropic_boundary_coincidence_trace S θ hS).symm
  have hpair := (isotropic_negative_prime_trace_unique hp hp7 hx hconstraint hr he).1
  rw [isotropic_exponential_trace, ← hpoint] at hpair
  have hre := congrArg Complex.re hpair
  simp only [Complex.ofReal_re] at hre
  linarith

theorem isotropic_cosine_pair_centers {α θ : ℝ}
    (hα : α ∈ Set.Icc 0 Real.pi) (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi)
    (hcos : Real.cos θ = Real.cos α) : θ = α ∨ θ = -α := by
  have habs : |θ| = α := Real.injOn_cos
    ⟨abs_nonneg θ, abs_le.mpr hθ⟩ hα (by simpa only [Real.cos_abs] using hcos)
  rcases le_total 0 θ with h | h
  · left; simpa only [abs_of_nonneg h] using habs
  · right; rw [abs_of_nonpos h] at habs; linarith

end
end IsingBulk.AnisoF002.Isotropic
