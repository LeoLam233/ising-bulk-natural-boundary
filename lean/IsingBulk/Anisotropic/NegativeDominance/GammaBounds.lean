import IsingBulk.Anisotropic.NegativeDominance.ExactGamma

/-! Uniform finite-error bounds for the exact Gamma factor. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

/-- Uniform scalar logarithm bound, with no fixed-index limit. -/
theorem neg_log_one_sub_div_bounds {m a j : ℝ}
    (hm : 0 ≤ m) (hma : m ≤ a) (haj : a < j) :
    0 ≤ -Real.log (1 - m / j) ∧ -Real.log (1 - m / j) ≤ a / (j - a) := by
  have ha : 0 ≤ a := le_trans hm hma
  have hj : 0 < j := lt_of_le_of_lt ha haj
  have hmj : m < j := lt_of_le_of_lt hma haj
  have hx : 0 < 1 - m / j := by
    have := (div_lt_one hj).mpr hmj
    linarith
  have hxle : 1 - m / j ≤ 1 := by linarith [div_nonneg hm hj.le]
  constructor
  · have := Real.log_nonpos hx.le hxle
    linarith
  · have hh := Real.one_sub_inv_le_log_of_pos hx
    have he : (1 - m / j)⁻¹ - 1 = m / (j - m) := by
      field_simp [hj.ne', (sub_pos.mpr hmj).ne']
      ring
    have hbound : m / (j - m) ≤ a / (j - a) := by
      gcongr
    linarith

/-- The full finite correction in (5.28) is nonnegative and bounded
uniformly by `a²/(j-a)`. In particular its scale is `O(a²/j)` when
`a/j` is bounded away from one. -/
theorem gamma_log_correction_bounds (a j : ℕ) (haj : a < j) :
    let correction := -∑ m ∈ Finset.range a, Real.log (1 - (m : ℝ) / j)
    0 ≤ correction ∧ correction ≤ (a : ℝ)^2 / ((j : ℝ) - a) := by
  dsimp
  have hcast : (a : ℝ) < j := by exact_mod_cast haj
  have hb (m : ℕ) (hm : m ∈ Finset.range a) :=
    neg_log_one_sub_div_bounds (show (0 : ℝ) ≤ m by positivity)
      (show (m : ℝ) ≤ a by exact_mod_cast (Finset.mem_range.mp hm).le) hcast
  rw [← Finset.sum_neg_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro m hm
    exact (hb m hm).1
  · calc
      ∑ m ∈ Finset.range a, -Real.log (1 - (m : ℝ) / j) ≤
          ∑ _m ∈ Finset.range a, (a : ℝ) / ((j : ℝ) - a) :=
        Finset.sum_le_sum (fun m hm => (hb m hm).2)
      _ = (a : ℝ)^2 / ((j : ℝ) - a) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

/-- Quantitative exact-Gamma versus power-law logarithmic error. -/
theorem log_gamma_jet_error_bounds (a j : ℕ) (haj : a < j) :
    0 ≤ Real.log (Real.Gamma ((j : ℝ) + 1 - a) / Real.Gamma ((j : ℝ) + 1)) +
        a * Real.log j ∧
    Real.log (Real.Gamma ((j : ℝ) + 1 - a) / Real.Gamma ((j : ℝ) + 1)) +
        a * Real.log j ≤ (a : ℝ)^2 / ((j : ℝ) - a) := by
  rw [log_gamma_jet_ratio a j haj.le (lt_of_le_of_lt (Nat.zero_le a) haj)]
  have hb := gamma_log_correction_bounds a j haj
  dsimp at hb
  constructor <;> linarith [hb.1, hb.2]

end
end IsingBulk.Anisotropic.NegativeDominance
