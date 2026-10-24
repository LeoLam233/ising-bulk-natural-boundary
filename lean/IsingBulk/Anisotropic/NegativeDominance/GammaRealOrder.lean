import IsingBulk.Anisotropic.NegativeDominance.GammaDifferences
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Exact real-order interpolation of the finite Gamma quotient and its
order derivative. This avoids differentiating a fixed-index asymptotic. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

def gammaLogRealOrder (a : ℕ) (j : ℝ) : ℝ :=
  -∑ m ∈ Finset.range a, Real.log (j - (m : ℝ))

theorem gammaLogRealOrder_eq_correction (a : ℕ) (j : ℝ) (h : (a : ℝ) < j) :
    gammaLogRealOrder a j = -(a : ℝ) * Real.log j + gammaCorrection a j := by
  have hj : 0 < j := lt_of_le_of_lt (Nat.cast_nonneg a) h
  have he (m : ℕ) (hm : m ∈ Finset.range a) :
      Real.log (j - (m : ℝ)) = Real.log j + Real.log (1 - (m : ℝ) / j) := by
    have hmj : (m : ℝ) < j := lt_trans (by exact_mod_cast Finset.mem_range.mp hm) h
    have hpos : 0 < 1 - (m : ℝ) / j := by linarith [(div_lt_one hj).mpr hmj]
    rw [← Real.log_mul hj.ne' hpos.ne']
    congr 1
    field_simp
  unfold gammaLogRealOrder gammaCorrection cumulative
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Finset.sum_neg_distrib]
  ring

/-- Identification with the exact integer-order Gamma quotient. -/
theorem gammaLogRealOrder_eq_log_gamma (a j : ℕ) (h : a < j) :
    gammaLogRealOrder a j =
      Real.log (Real.Gamma ((j : ℝ) + 1 - a) / Real.Gamma ((j : ℝ) + 1)) := by
  rw [gammaLogRealOrder_eq_correction a j (by exact_mod_cast h),
    log_gamma_jet_ratio a j (Nat.le_of_lt h) (lt_of_le_of_lt (Nat.zero_le a) h)]
  unfold gammaCorrection cumulative
  rw [Finset.sum_neg_distrib]
  ring

/-- The exact real-order logarithmic derivative, for every growing exponent. -/
theorem hasDerivAt_gammaLogRealOrder (a : ℕ) (j : ℝ) (h : (a : ℝ) < j) :
    HasDerivAt (gammaLogRealOrder a)
      (-∑ m ∈ Finset.range a, (j - (m : ℝ))⁻¹) j := by
  have hd (m : ℕ) (hm : m ∈ Finset.range a) :
      HasDerivAt (fun x : ℝ => Real.log (x - (m : ℝ))) (j - (m : ℝ))⁻¹ j := by
    have hmj : (m : ℝ) < j := lt_trans (by exact_mod_cast Finset.mem_range.mp hm) h
    simpa [Function.comp_def] using (Real.hasDerivAt_log (sub_pos.mpr hmj).ne').comp j
      ((hasDerivAt_id j).sub_const (m : ℝ))
  exact (HasDerivAt.fun_sum hd).neg

/-- The reciprocal sum controlling changes of real derivative order is
bounded uniformly in both particle exponents. -/
theorem reciprocal_order_sum_bounds (a b : ℕ) (j : ℝ)
    (h : ((a + b : ℕ) : ℝ) < j) :
    (b : ℝ) / j ≤ ∑ k ∈ Finset.range b, (j - ((a + k : ℕ) : ℝ))⁻¹ ∧
    (∑ k ∈ Finset.range b, (j - ((a + k : ℕ) : ℝ))⁻¹) ≤
      (b : ℝ) / (j - ((a + b : ℕ) : ℝ)) := by
  have hj : 0 < j := lt_of_le_of_lt (Nat.cast_nonneg (a + b)) h
  have hd : 0 < j - ((a + b : ℕ) : ℝ) := sub_pos.mpr h
  have hp (k : ℕ) (hk : k ∈ Finset.range b) :
      1 / j ≤ (j - ((a + k : ℕ) : ℝ))⁻¹ ∧
      (j - ((a + k : ℕ) : ℝ))⁻¹ ≤ 1 / (j - ((a + b : ℕ) : ℝ)) := by
    have hab : ((a + k : ℕ) : ℝ) ≤ ((a + b : ℕ) : ℝ) := by
      exact_mod_cast (by have := Finset.mem_range.mp hk; omega : a + k ≤ a + b)
    have hpos : 0 < j - ((a + k : ℕ) : ℝ) := by linarith
    rw [← one_div]
    constructor
    · apply one_div_le_one_div_of_le hpos
      have := Nat.cast_nonneg (α := ℝ) (a + k)
      linarith
    · apply one_div_le_one_div_of_le hd
      linarith
  constructor
  · calc
      (b : ℝ) / j = ∑ _k ∈ Finset.range b, 1 / j := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum (fun k hk => (hp k hk).1)
  · calc
      _ ≤ ∑ _k ∈ Finset.range b, 1 / (j - ((a + b : ℕ) : ℝ)) :=
        Finset.sum_le_sum (fun k hk => (hp k hk).2)
      _ = _ := by simp [div_eq_mul_inv]

end
end IsingBulk.Anisotropic.NegativeDominance
