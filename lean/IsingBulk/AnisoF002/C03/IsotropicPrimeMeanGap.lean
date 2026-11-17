import IsingBulk.AnisoF002.C03.IsotropicPrimeBranchGap
import IsingBulk.AnisoF002.C03.IsotropicConstrainedMeans

/-!
# The original constrained means avoid the branch corner

Every integer lift of both physical signs is included. On any finite
set of lifts the exact non-root-of-unity statement supplies a strictly
positive distance, before selecting a local angular radius.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section

theorem isotropic_exponential_of_integer_mean (N : ℕ) (θ a : ℝ) (l : ℤ)
    (hmean : (N : ℝ) * θ = 2 * Real.pi * l + a) :
    Complex.exp ((θ : ℂ) * Complex.I) ^ N = Complex.exp ((a : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  have he : (N : ℂ) * ((θ : ℂ) * Complex.I) =
      (l : ℂ) * (2 * Real.pi * Complex.I) + (a : ℂ) * Complex.I := by
    have hc := congrArg (fun r : ℝ => (r : ℂ)) hmean
    push_cast at hc
    linear_combination hc * Complex.I
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

theorem isotropic_prime_constrained_mean_ne_zero {p r : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hr : r.Coprime p)
    {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : a = 0 ∨ a = Real.pi) (l : ℤ) :
    constrainedRightMean N (isotropicPrimeBranchAngle p r) a l ≠ 0 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  intro hz
  have hm : (N : ℝ) * constrainedRightMean N (isotropicPrimeBranchAngle p r) a l =
      (N : ℝ) * isotropicPrimeBranchAngle p r + 2 * Real.pi * l + a := by
    unfold constrainedRightMean
    field_simp
    ring
  rw [hz, mul_zero] at hm
  have hmean : (N : ℝ) * (-isotropicPrimeBranchAngle p r) = 2 * Real.pi * l + a := by
    linarith
  have he := isotropic_exponential_of_integer_mean N (-isotropicPrimeBranchAngle p r) a l hmean
  rw [Complex.ofReal_neg] at he
  change isotropicPrimeBranchRoot p r ^ N = Complex.exp ((a : ℂ) * Complex.I) at he
  rcases ha with rfl | rfl
  · apply isotropicPrimeBranchRoot_pow_ne_one hp hp5 hr hN
    simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero] using he
  · apply isotropicPrimeBranchRoot_pow_ne_neg_one hp hp5 hr hN
    simpa only [Complex.exp_pi_mul_I] using he

theorem exists_isotropic_prime_finite_mean_gap {p r : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hr : r.Coprime p)
    {N : ℕ} (hN : 0 < N) {a : ℝ} (ha : a = 0 ∨ a = Real.pi) (L : Finset ℤ) :
    ∃ g : ℝ, 0 < g ∧ ∀ l ∈ L,
      g ≤ |constrainedRightMean N (isotropicPrimeBranchAngle p r) a l| := by
  classical
  induction L using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert l L _ ih =>
    obtain ⟨g, hg, hbound⟩ := ih
    have hl : 0 < |constrainedRightMean N (isotropicPrimeBranchAngle p r) a l| :=
      abs_pos.mpr (isotropic_prime_constrained_mean_ne_zero hp hp5 hr hN ha l)
    refine ⟨min g |constrainedRightMean N (isotropicPrimeBranchAngle p r) a l|,
      lt_min hg hl, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hbound j hj)

end
end IsingBulk.AnisoF002.Isotropic
