import IsingBulk.Anisotropic.NegativeDominance.PhysicalMiddleDominance
import Mathlib.Analysis.SpecificLimits.Normed

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

theorem norm_le_of_log_gap (z w : ℂ) (hw : w ≠ 0) (a : ℝ) (k : ℕ)
    (h : Real.log ‖z‖ ≤ Real.log ‖w‖-a*(k : ℝ)) :
    ‖z‖ ≤ ‖w‖*Real.exp (-a)^k := by
  by_cases hz : z=0
  · simp only [hz, norm_zero]
    positivity
  have he := Real.exp_le_exp.mpr h
  rw [Real.exp_log (norm_pos_iff.mpr hz), sub_eq_add_neg, Real.exp_add,
    Real.exp_log (norm_pos_iff.mpr hw)] at he
  have hp : Real.exp (-(a*(k : ℝ))) = Real.exp (-a)^k := by
    rw [← neg_mul, mul_comm, Real.exp_nat_mul]
  rwa [hp] at he

theorem finite_geometric_tail (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (S : Finset ℕ) (hS : 0 ∉ S) :
    ∑ k ∈ S, r^k ≤ r/(1-r) := by
  have hs := summable_geometric_of_abs_lt_one (r := r) (by simpa [abs_of_nonneg hr] using hr1)
  have hh := hs.sum_le_tsum (insert 0 S) (fun k _ => pow_nonneg hr k)
  rw [Finset.sum_insert hS, pow_zero,
    tsum_geometric_of_abs_lt_one (by simpa [abs_of_nonneg hr] using hr1)] at hh
  have he : (1-r)⁻¹-1=r/(1-r) := by field_simp [ne_of_gt (sub_pos.mpr hr1)]; ring
  linarith only [hh, he]

/-- An arbitrary finite collection of competing complex terms is controlled
by the entire geometric tail; phases are not assumed equal. -/
theorem finite_norm_sum_of_log_gaps (z : ℕ → ℂ) (w : ℂ) (hw : w ≠ 0)
    (a : ℝ) (ha : 0 < a) (S : Finset ℕ) (hS : 0 ∉ S)
    (hgap : ∀ k ∈ S, Real.log ‖z k‖ ≤ Real.log ‖w‖-a*(k : ℝ)) :
    ∑ k ∈ S, ‖z k‖ ≤ ‖w‖*(Real.exp (-a)/(1-Real.exp (-a))) := by
  have hr : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
  have hr1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  calc
    ∑ k ∈ S, ‖z k‖ ≤ ∑ k ∈ S, ‖w‖*Real.exp (-a)^k :=
      Finset.sum_le_sum (fun k hk => norm_le_of_log_gap _ _ hw a k (hgap k hk))
    _ = ‖w‖*(∑ k ∈ S, Real.exp (-a)^k) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_geometric_tail _ hr hr1 S hS) (norm_nonneg _)

end
end IsingBulk.Anisotropic.NegativeDominance
