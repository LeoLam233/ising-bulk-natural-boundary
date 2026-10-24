import IsingBulk.Anisotropic.NegativeDominance.GammaRealOrder

/-! The exact real-order balance function underlying integer-order selection.
Its constants collect j-independent model factors; no Stirling truncation is
used in the order-dependent part. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

/-- `slope` is log(τ_lower/τ_upper); `constant` contains only factors
independent of derivative order. -/
def orderBalance (constant slope : ℝ) (a b : ℕ) (j : ℝ) : ℝ :=
  constant + j * slope + gammaLogRealOrder (a + b) j - gammaLogRealOrder a j

theorem hasDerivAt_orderBalance (constant slope : ℝ) (a b : ℕ) (j : ℝ)
    (h : ((a + b : ℕ) : ℝ) < j) :
    HasDerivAt (orderBalance constant slope a b)
      (slope - ∑ k ∈ Finset.range b, (j - ((a + k : ℕ) : ℝ))⁻¹) j := by
  have ha : (a : ℝ) < j := lt_of_le_of_lt (by exact_mod_cast Nat.le_add_right a b) h
  have hh := (((hasDerivAt_id j).mul_const slope).const_add constant).add
    (hasDerivAt_gammaLogRealOrder (a + b) j h)
  have hh' := hh.sub (hasDerivAt_gammaLogRealOrder a j ha)
  convert hh' using 1
  · rfl
  · rw [Finset.sum_range_add]
    ring

/-- Uniform bounds on the exact order derivative. -/
theorem deriv_orderBalance_bounds (constant slope : ℝ) (a b : ℕ) (j : ℝ)
    (h : ((a + b : ℕ) : ℝ) < j) :
    slope - (b : ℝ) / (j - ((a + b : ℕ) : ℝ)) ≤
      deriv (orderBalance constant slope a b) j ∧
    deriv (orderBalance constant slope a b) j ≤ slope - (b : ℝ) / j := by
  rw [(hasDerivAt_orderBalance constant slope a b j h).deriv]
  have hb := reciprocal_order_sum_bounds a b j h
  constructor <;> linarith [hb.1, hb.2]

end
end IsingBulk.Anisotropic.NegativeDominance
