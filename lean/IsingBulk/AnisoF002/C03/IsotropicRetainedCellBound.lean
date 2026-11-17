import IsingBulk.AnisoF002.C03.IsotropicRetainedPairs

/-!
# Gaussian cell counting with retained collision coefficients

Replacing any finite set of complete pairs by their analytic collision
coefficients costs a fixed factor per retained pair. Every unretained
pair remains in the product and in the Gaussian count.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped BigOperators

theorem retained_cell_product_bound {N K : ℕ} (c : Fin N → Fin K)
    (P A : Fin N → Fin N → ℂ) (R : Finset (Fin N × Fin N)) (hR : R ⊆ indexPairs N)
    (a b C : ℝ) (hK : 0 < K) (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 < C)
    (hwithin : ∀ i j, i < j → c i = c j → ‖P i j‖ ≤ Real.exp (-a))
    (hall : ∀ i j, i < j → ‖P i j‖ ≤ Real.exp b)
    (hcoeff : ∀ ij ∈ R, ‖A ij.1 ij.2‖ ≤ C) :
    ‖(∏ ij ∈ R, A ij.1 ij.2) * ∏ ij ∈ indexPairs N \ R, P ij.1 ij.2‖ ≤
      (C / Real.exp (-a)) ^ R.card *
        Real.exp (-(a + b - K * b) / (2 * K) * (N : ℝ) ^ 2 + a / 2 * N) := by
  classical
  let μ := Real.exp (-a) / C
  have hμ : 0 < μ := div_pos (Real.exp_pos _) hC
  have hμC : μ * C = Real.exp (-a) := div_mul_cancel₀ _ hC.ne'
  let Q : Fin N → Fin N → ℂ := fun i j =>
    if (i, j) ∈ R then (μ : ℂ) * A i j else P i j
  have hret : ∀ i j, (i, j) ∈ R → ‖Q i j‖ ≤ Real.exp (-a) := by
    intro i j hij
    simp only [Q, ite_eq_left hij, norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ.le]
    exact (mul_le_mul_of_nonneg_left (hcoeff (i, j) hij) hμ.le).trans_eq hμC
  have hQwithin : ∀ i j, i < j → c i = c j → ‖Q i j‖ ≤ Real.exp (-a) := by
    intro i j hij hc
    by_cases h : (i, j) ∈ R
    · exact hret i j h
    · simpa only [Q, ite_eq_right h] using hwithin i j hij hc
  have hQall : ∀ i j, i < j → ‖Q i j‖ ≤ Real.exp b := by
    intro i j hij
    by_cases h : (i, j) ∈ R
    · exact (hret i j h).trans (Real.exp_le_exp.mpr (by linarith))
    · simpa only [Q, ite_eq_right h] using hall i j hij
  have hbound := complete_pair_product_bound c Q a b hK ha hb hQwithin hQall
  have hprod : (∏ ij ∈ indexPairs N, Q ij.1 ij.2) =
      (μ : ℂ) ^ R.card *
        ((∏ ij ∈ R, A ij.1 ij.2) * ∏ ij ∈ indexPairs N \ R, P ij.1 ij.2) := by
    rw [← Finset.prod_sdiff hR]
    have h₁ : (∏ ij ∈ indexPairs N \ R, Q ij.1 ij.2) =
        ∏ ij ∈ indexPairs N \ R, P ij.1 ij.2 := by
      apply Finset.prod_congr rfl
      intro ij hij
      exact ite_eq_right (Finset.mem_sdiff.mp hij).2
    have h₂ : (∏ ij ∈ R, Q ij.1 ij.2) =
        ∏ ij ∈ R, (μ : ℂ) * A ij.1 ij.2 := by
      apply Finset.prod_congr rfl
      intro ij hij
      exact ite_eq_left hij
    rw [h₁, h₂, Finset.prod_mul_distrib, Finset.prod_const]
    ring
  rw [hprod, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hμ.le] at hbound
  rw [mul_comm (μ ^ R.card)] at hbound
  have h := (le_div_iff₀ (pow_pos hμ R.card)).mpr hbound
  simpa only [μ, div_eq_mul_inv, mul_inv_rev, inv_inv, inv_pow, mul_pow, mul_comm] using h

end IsingBulk.AnisoF002.Isotropic
