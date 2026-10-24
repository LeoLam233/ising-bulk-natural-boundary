import IsingBulk.Anisotropic.NegativeDominance.GammaBounds
import IsingBulk.Anisotropic.NegativeDominance.CumulativeDifferences

/-! Exact-factor second differences of the Gamma correction, with estimates
uniform in the derivative order and the growing particle shift. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

/-- Quantitative finite-difference bound for an individual logarithm. -/
theorem neg_log_increment_bounds {x y A j : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hyA : y ≤ A) (hAj : A < j) :
    0 ≤ -Real.log (1 - y / j) + Real.log (1 - x / j) ∧
    -Real.log (1 - y / j) + Real.log (1 - x / j) ≤ (y - x) / (j - A) := by
  have hy : 0 ≤ y := hx.trans hxy
  have hj : 0 < j := lt_of_le_of_lt (hy.trans hyA) hAj
  have hxj : x < j := lt_of_le_of_lt (hxy.trans hyA) hAj
  have hyj : y < j := lt_of_le_of_lt hyA hAj
  have hxp : 0 < 1 - x / j := by linarith [(div_lt_one hj).mpr hxj]
  have hyp : 0 < 1 - y / j := by linarith [(div_lt_one hj).mpr hyj]
  have horder : 1 - y / j ≤ 1 - x / j := by gcongr
  constructor
  · have hh := Real.log_le_log hyp horder
    linarith
  · have hh := Real.log_le_sub_one_of_pos (div_pos hxp hyp)
    rw [Real.log_div hxp.ne' hyp.ne'] at hh
    have he : (1 - x / j) / (1 - y / j) - 1 = (y - x) / (j - y) := by
      field_simp [hj.ne', (sub_pos.mpr hyj).ne']
      ring
    rw [he] at hh
    have hb : (y - x) / (j - y) ≤ (y - x) / (j - A) := by gcongr
    linarith

def gammaCorrection (a : ℕ) (j : ℝ) : ℝ :=
  cumulative (fun m => -Real.log (1 - (m : ℝ) / j)) a

/-- Uniform control of the second difference with unequal adjacent shifts.
For α_{n-d}, α_n, α_{n+d}, take `b=dn-d²/2`, `d=d²`.
This is a proved bound on the exact finite correction, not on a discarded
Stirling remainder. -/
theorem gammaCorrection_second_difference_bounds (a b d : ℕ) (j : ℝ)
    (h : ((a + 2 * b + d : ℕ) : ℝ) < j) :
    let D := gammaCorrection (a + 2 * b + d) j -
      2 * gammaCorrection (a + b) j + gammaCorrection a j
    0 ≤ D ∧ D ≤ ((b : ℝ)^2 + d * ((a + 2 * b + d : ℕ) : ℝ)) /
      (j - ((a + 2 * b + d : ℕ) : ℝ)) := by
  dsimp
  let A : ℝ := ((a + 2 * b + d : ℕ) : ℝ)
  have hA : A < j := h
  have hp (k : ℕ) (hk : k < b) :
      0 ≤ -Real.log (1 - ((a + b + k : ℕ) : ℝ) / j) +
        Real.log (1 - ((a + k : ℕ) : ℝ) / j) ∧
      -Real.log (1 - ((a + b + k : ℕ) : ℝ) / j) +
        Real.log (1 - ((a + k : ℕ) : ℝ) / j) ≤ (b : ℝ) / (j - A) := by
    have hxy : ((a + k : ℕ) : ℝ) ≤ ((a + b + k : ℕ) : ℝ) := by exact_mod_cast (by omega : a + k ≤ a + b + k)
    have hyA : ((a + b + k : ℕ) : ℝ) ≤ A := by
      dsimp [A]
      exact_mod_cast (by omega : a + b + k ≤ a + 2 * b + d)
    have hh := neg_log_increment_bounds (by positivity) hxy hyA hA
    have he : ((a + b + k : ℕ) : ℝ) - ((a + k : ℕ) : ℝ) = b := by push_cast; ring
    simpa only [he] using hh
  have he (k : ℕ) (hk : k < d) :
      0 ≤ -Real.log (1 - ((a + 2 * b + k : ℕ) : ℝ) / j) ∧
      -Real.log (1 - ((a + 2 * b + k : ℕ) : ℝ) / j) ≤ A / (j - A) := by
    apply neg_log_one_sub_div_bounds (by positivity) _ hA
    dsimp [A]
    exact_mod_cast (by omega : a + 2 * b + k ≤ a + 2 * b + d)
  constructor
  · unfold gammaCorrection
    rw [cumulative_second_difference]
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro k hk
      simpa only [sub_neg_eq_add] using (hp k (Finset.mem_range.mp hk)).1
    · apply Finset.sum_nonneg
      intro k hk
      exact (he k (Finset.mem_range.mp hk)).1
  · have hb := cumulative_second_difference_le
      (fun m => -Real.log (1 - (m : ℝ) / j)) a b d (1 / (j - A)) (A / (j - A))
      (fun k hk => by simpa only [sub_neg_eq_add, mul_one_div] using (hp k hk).2)
      (fun k hk => (he k hk).2)
    unfold gammaCorrection
    calc
      _ ≤ (b : ℝ)^2 * (1 / (j - A)) + d * (A / (j - A)) := hb
      _ = _ := by dsimp [A]; ring

end
end IsingBulk.Anisotropic.NegativeDominance
