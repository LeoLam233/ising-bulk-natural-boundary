import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic

namespace IsingBulk.Anisotropic.NegativeDominance
open Filter
open scoped Topology

/-- The same tail estimates force absolute convergence of the limiting
series; the totalized infinite sum is not being used as a substitute. -/
theorem summable_of_summable_tail_limit {ι : Type*} {l : Filter ι} [NeBot l]
    {f : ι → ℕ → ℂ} {g : ℕ → ℂ} (K : ℕ) {G : ℕ → ℝ}
    (hG : Summable G) (hf : ∀ n, Tendsto (fun t => f t n) l (𝓝 (g n)))
    (hbound : ∀ᶠ t in l, ∀ k, ‖f t (k+K)‖≤G k) :
    Summable (fun n => ‖g n‖) := by
  apply (summable_nat_add_iff K).mp
  apply hG.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  exact le_of_tendsto (hf (k+K)).norm (hbound.mono (fun _ ht => ht k))

/-- A summable tail majorant and individual limits suffice for the complete
infinite sum, with the exceptional finite initial segment handled internally. -/
theorem tendsto_tsum_of_summable_tail {ι : Type*} {l : Filter ι}
    {f : ι → ℕ → ℂ} {g : ℕ → ℂ} (K : ℕ) {G : ℕ → ℝ}
    (hG : Summable G) (hf : ∀ n, Tendsto (fun t => f t n) l (𝓝 (g n)))
    (hbound : ∀ᶠ t in l, ∀ k, ‖f t (k+K)‖≤G k) :
    Tendsto (fun t => ∑' n, f t n) l (𝓝 (∑' n, g n)) := by
  let R : ℕ → ℝ := fun n => if n<K then ‖g n‖+1 else G (n-K)
  have hR : Summable R := by
    apply (summable_nat_add_iff K).mp
    simpa [R] using hG
  have hlo : ∀ᶠ t in l, ∀ n∈Finset.range K, ‖f t n‖≤‖g n‖+1 := by
    rw [eventually_all_finset]
    intro n _
    exact ((hf n).norm.eventually (gt_mem_nhds (lt_add_one _))).mono (fun _ ht => ht.le)
  apply tendsto_tsum_of_dominated_convergence hR hf
  filter_upwards [hbound,hlo] with t ht hlo n
  by_cases hn : n<K
  · simpa [R,hn] using hlo n (Finset.mem_range.mpr hn)
  · have hh := ht (n-K)
    rw [Nat.sub_add_cancel (Nat.le_of_not_gt hn)] at hh
    simpa [R,hn] using hh

/-- Uniform summable majorant including the finite initial terms. -/
theorem exists_summable_bound_of_summable_tail {ι : Type*} {l : Filter ι}
    {f : ι → ℕ → ℂ} {g : ℕ → ℂ} (K : ℕ) {G : ℕ → ℝ}
    (hG : Summable G) (hf : ∀ n, Tendsto (fun t => f t n) l (𝓝 (g n)))
    (hbound : ∀ᶠ t in l, ∀ k, ‖f t (k+K)‖≤G k) :
    ∃ R : ℕ → ℝ, Summable R ∧ ∀ᶠ t in l, ∀ n, ‖f t n‖≤R n := by
  let R : ℕ → ℝ := fun n => if n<K then ‖g n‖+1 else G (n-K)
  have hR : Summable R := by
    apply (summable_nat_add_iff K).mp
    simpa [R] using hG
  have hlo : ∀ᶠ t in l, ∀ n∈Finset.range K, ‖f t n‖≤‖g n‖+1 := by
    rw [eventually_all_finset]
    intro n _
    exact ((hf n).norm.eventually (gt_mem_nhds (lt_add_one _))).mono (fun _ ht => ht.le)
  refine ⟨R,hR,?_⟩
  filter_upwards [hbound,hlo] with t ht hlo n
  by_cases hn : n<K
  · simpa [R,hn] using hlo n (Finset.mem_range.mpr hn)
  · have hh := ht (n-K)
    rw [Nat.sub_add_cancel (Nat.le_of_not_gt hn)] at hh
    simpa [R,hn] using hh

end IsingBulk.Anisotropic.NegativeDominance
