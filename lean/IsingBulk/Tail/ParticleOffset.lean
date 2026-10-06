import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

namespace IsingBulk.Tail
noncomputable section

def particleOffset (k : ℕ) (f : ℕ → ℝ) (N : ℕ) : ℝ := if k ≤ N then f (N-k) else 0

theorem particleOffset_add (k : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    particleOffset k f (n+k)=f n := by simp [particleOffset]

theorem particleOffset_summable (k : ℕ) {f : ℕ → ℝ} (hf : Summable f) :
    Summable (particleOffset k f) := by
  apply (summable_nat_add_iff k).mp
  simpa only [particleOffset_add] using hf

theorem particleOffset_tsum (k : ℕ) {f : ℕ → ℝ} (hf : Summable f) :
    ∑' N, particleOffset k f N = ∑' n, f n := by
  have hh := (particleOffset_summable k hf).sum_add_tsum_nat_add k
  have hzero : ∑ i ∈ Finset.range k, particleOffset k f i=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [particleOffset,not_le.mpr (Finset.mem_range.mp hi),ite_false]
  simpa only [hzero,zero_add,particleOffset_add] using hh.symm

theorem particleOffset_nonneg (k : ℕ) {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (N : ℕ) :
    0 ≤ particleOffset k f N := by
  unfold particleOffset
  split_ifs
  · exact hf _
  · exact le_rfl

end
end IsingBulk.Tail
