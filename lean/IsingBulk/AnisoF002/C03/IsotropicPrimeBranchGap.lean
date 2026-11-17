import IsingBulk.AnisoF002.C03.IsotropicPrimeGeometry

/-!
# Non-root-of-unity branch points at the actual prime family

The branch angle is exactly arccos(|2 cos alpha| - 1).  Every positive
integer power of its unit root differs from both determinant signs.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section

theorem isotropic_exponential_trace (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) +
      (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ = (2 * Real.cos θ : ℝ) := by
  rw [← Complex.exp_neg]
  rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

def isotropicPrimeBranchAngle (p a : ℕ) : ℝ :=
  Real.arccos (|2 * Real.cos (isotropicPrimeAngle p a)| - 1)

def isotropicPrimeBranchRoot (p a : ℕ) : ℂ :=
  Complex.exp (-(isotropicPrimeBranchAngle p a : ℂ) * Complex.I)

theorem isotropicPrimeBranchRoot_trace (p a : ℕ) :
    isotropicPrimeBranchRoot p a + (isotropicPrimeBranchRoot p a)⁻¹ =
      (2 * (|2 * Real.cos (isotropicPrimeAngle p a)| - 1) : ℝ) := by
  have hupper : |2 * Real.cos (isotropicPrimeAngle p a)| - 1 ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [Real.abs_cos_le_one (isotropicPrimeAngle p a)]
  have hlower : -1 ≤ |2 * Real.cos (isotropicPrimeAngle p a)| - 1 := by
    linarith [abs_nonneg (2 * Real.cos (isotropicPrimeAngle p a))]
  convert isotropic_exponential_trace (-isotropicPrimeBranchAngle p a) using 1
  · simp only [isotropicPrimeBranchRoot, Complex.ofReal_neg]
  · rw [Real.cos_neg, isotropicPrimeBranchAngle, Real.cos_arccos hlower hupper]

theorem isotropicPrimeBranchRoot_pow_ne_one {p a : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ha : a.Coprime p) {q : ℕ} (hq : 0 < q) :
    isotropicPrimeBranchRoot p a ^ q ≠ 1 := by
  have hx := isotropicPrimeRoot_primitive hp.pos ha
  by_cases hS : 0 ≤ 2 * Real.cos (isotropicPrimeAngle p a)
  · obtain ⟨y, hy, hneg⟩ := exists_isotropic_negative_primitive_trace hp hp5
    apply isotropic_primitive_trace_branch_gap hp.pos hq hx hy 1
    · simpa only [Rat.cast_one, one_mul] using hneg
    · rw [isotropicPrimeBranchRoot_trace, isotropicPrimeRoot_trace, abs_of_nonneg hS]
      push_cast
      ring
  · obtain ⟨y, hy, hpos⟩ := exists_isotropic_positive_primitive_trace hp hp5
    apply isotropic_primitive_trace_branch_gap hp.pos hq hx hy (-1)
    · simpa only [Rat.cast_neg, Rat.cast_one, neg_one_mul, Complex.neg_re,
        neg_lt_zero] using hpos
    · rw [isotropicPrimeBranchRoot_trace, isotropicPrimeRoot_trace,
        abs_of_neg (lt_of_not_ge hS)]
      push_cast
      ring

theorem isotropicPrimeBranchRoot_pow_ne_neg_one {p a : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ha : a.Coprime p) {q : ℕ} (hq : 0 < q) :
    isotropicPrimeBranchRoot p a ^ q ≠ -1 := by
  intro he
  apply isotropicPrimeBranchRoot_pow_ne_one hp hp5 ha (Nat.mul_pos hq (by omega : 0 < 2))
  rw [pow_mul, he]
  norm_num

end
end IsingBulk.AnisoF002.Isotropic
