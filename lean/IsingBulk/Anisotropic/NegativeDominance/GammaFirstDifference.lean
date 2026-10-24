import IsingBulk.Anisotropic.NegativeDominance.GammaDifferences

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

theorem gammaCorrection_step_bounds (a b : ℕ) (j : ℝ) (h : ((a+b : ℕ) : ℝ) < j) :
    0 ≤ gammaCorrection (a+b) j-gammaCorrection a j ∧
      gammaCorrection (a+b) j-gammaCorrection a j ≤
        (b : ℝ)*((a+b : ℕ) : ℝ)/(j-((a+b : ℕ) : ℝ)) := by
  have he : gammaCorrection (a+b) j-gammaCorrection a j =
      ∑ k ∈ Finset.range b, -Real.log (1-((a+k : ℕ) : ℝ)/j) := by
    unfold gammaCorrection
    rw [cumulative_add]
    ring
  rw [he]
  have hb (k : ℕ) (hk : k ∈ Finset.range b) :=
    neg_log_one_sub_div_bounds (show (0 : ℝ) ≤ (a+k : ℕ) by positivity)
      (show ((a+k : ℕ) : ℝ) ≤ (a+b : ℕ) by exact_mod_cast (by have := Finset.mem_range.mp hk; omega : a+k ≤ a+b)) h
  constructor
  · exact Finset.sum_nonneg (fun k hk => (hb k hk).1)
  · calc
      _ ≤ ∑ _k ∈ Finset.range b, ((a+b : ℕ) : ℝ)/(j-((a+b : ℕ) : ℝ)) :=
        Finset.sum_le_sum (fun k hk => (hb k hk).2)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end
end IsingBulk.Anisotropic.NegativeDominance
