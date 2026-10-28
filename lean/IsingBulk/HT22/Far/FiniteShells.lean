import IsingBulk.HT22.Tail.ShellScale
import IsingBulk.Preferred22.ShellCover

/-! A particle-independent finite far prefix. The cutoff is chosen before
mean, epsilon, particle order, and derivative order. -/
namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22 Filter
open scoped Topology BigOperators ENNReal

theorem far_dyadic_prefix {δ : ℝ} (hδ : 0<δ) :
    ∃ K : ℕ, ∀ μ ε : ℝ, 0≤ε → ∀ k : ℕ,
      δ≤shellCoordinateScale μ (preferredDyadicRadius k) ε → k<K := by
  have ht : Tendsto preferredDyadicRadius atTop (𝓝 (0:ℝ)) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1)).const_mul Real.pi
    convert hh using 1
    · funext m
      unfold preferredDyadicRadius
      rw [pow_succ]
      ring
    · simp
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (sq_pos_of_pos hδ)))
  refine ⟨K,?_⟩
  intro μ ε hε k hfar
  have hdiam := shellCoordinateScale_far_diameter (preferredDyadicRadius_pos k) hε hδ.le hfar
  by_contra h
  exact (not_lt_of_ge hdiam) (hK k (Nat.le_of_not_gt h))

theorem far_dyadic_tsum_bound {δ : ℝ} (hδ : 0<δ) :
    ∃ K : ℕ, ∀ μ ε : ℝ, 0≤ε → ∀ f : ℕ → ℝ≥0∞, ∀ E : ℝ≥0∞,
      (∀ k, δ≤shellCoordinateScale μ (preferredDyadicRadius k) ε → f k≤E) →
      (∑' k, if δ≤shellCoordinateScale μ (preferredDyadicRadius k) ε then f k else 0)≤K*E := by
  obtain ⟨K,hK⟩ := far_dyadic_prefix hδ
  refine ⟨K,?_⟩
  intro μ ε hε f E hf
  let g : ℕ → ℝ≥0∞ := fun k => if δ≤shellCoordinateScale μ (preferredDyadicRadius k) ε then f k else 0
  have hs : ∀ k∉Finset.range K, g k=0 := by
    intro k hk
    have hn : ¬δ≤shellCoordinateScale μ (preferredDyadicRadius k) ε := by
      intro h
      exact hk (Finset.mem_range.mpr (hK μ ε hε k h))
    simp [g,hn]
  change (∑' k,g k)≤_
  rw [tsum_eq_sum hs]
  calc
    _ ≤ ∑ _k∈Finset.range K,E := by
      apply Finset.sum_le_sum
      intro k hk
      dsimp only [g]
      split_ifs with h
      · exact hf k h
      · exact bot_le
    _ = _ := by simp

end
end IsingBulk.HT22.Far
