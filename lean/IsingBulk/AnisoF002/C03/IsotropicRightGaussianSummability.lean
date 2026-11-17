import IsingBulk.AnisoF002.C03.IsotropicRightGaussianJets
import IsingBulk.AnisoF002.RegularTail.GaussianEnvelope

/-!
# Summability of the actual right-sector Gaussian coefficient envelope
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem summable_polynomial_geometric_gaussian (p : ℕ) {κ B : ℝ}
    (hκ : 0 < κ) (hB : 0 < B) :
    Summable (fun N : ℕ => (N : ℝ) ^ p * B ^ N *
      Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N)) := by
  apply (Real.summable_pow_mul_exp_neg_nat_mul p (show (0 : ℝ) < 1 / 2 by norm_num)).of_norm_bounded_eventually_nat
  have hlarge : ∀ᶠ N : ℕ in atTop, (Real.log B + 1) / κ ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlarge] with N hN
  have hmul : Real.log B + 1 ≤ κ * (N : ℝ) := by
    have hh := (div_le_iff₀ hκ).mp hN
    nlinarith only [hh]
  have hmulN := mul_le_mul_of_nonneg_right hmul (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hexponent : -κ * (N : ℝ) ^ 2 + (Real.log B + 1 / 2) * N ≤ -(1 / 2 : ℝ) * N := by
    nlinarith only [hmulN]
  have heq : B ^ N * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) =
      Real.exp (-κ * (N : ℝ) ^ 2 + (Real.log B + 1 / 2) * N) := by
    nth_rw 1 [← Real.exp_log hB]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc, heq]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by positivity)

theorem rightGaussianCoefficientEnvelope_summable {κ A B : ℝ}
    (hκ : 0 < κ) (hA : 0 ≤ A) (hB : 0 < B) (p : ℕ) :
    Summable (rightGaussianCoefficientEnvelope κ A B p) := by
  have hs := (summable_polynomial_geometric_gaussian p hκ hB).mul_left A
  apply hs.of_nonneg_of_le (fun N => rightGaussianCoefficientEnvelope_nonneg hA hB.le p N)
  intro N
  have hfactorial : (1 : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hangular : (1 : ℝ) ≤ (2 * Real.pi) ^ (N - 1) :=
    one_le_pow₀ (by linarith [Real.two_le_pi])
  have hden : (1 : ℝ) ≤ (N.factorial : ℝ) * (2 * Real.pi) ^ (N - 1) :=
    one_le_mul_of_one_le_of_one_le hfactorial hangular
  unfold rightGaussianCoefficientEnvelope
  calc
    _ ≤ A * (N : ℝ) ^ p * B ^ N * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) :=
      div_le_self (by positivity) hden
    _ = _ := by ring

end
end IsingBulk.AnisoF002.Isotropic
