import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Uniform dominated passage through the complete particle series. The
majorant is simultaneous in the approaching point and compact-family member. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open scoped Topology

/-- Uniform Tannery convergence on an arbitrary parameter set. This uses one
summable envelope on a common approaching neighborhood, not just bounds on the
boundary values or pointwise dominated-convergence statements. -/
theorem uniform_tsum_of_common_majorant {I E : Type*} {l : Filter I}
    (f : I→E→ℕ→ℂ) (g : E→ℕ→ℂ) (Q : Set E) (G : ℕ→ℝ)
    (hG : Summable G)
    (hg : ∀eta∈Q,∀n,‖g eta n‖≤G n)
    (hbound : ∀ᶠt in l,∀eta∈Q,∀n,‖f t eta n‖≤G n)
    (hlim : ∀n,TendstoUniformlyOn (fun t eta=>f t eta n) (fun eta=>g eta n) l Q) :
    TendstoUniformlyOn (fun t eta=>∑'n,f t eta n) (fun eta=>∑'n,g eta n) l Q := by
  let F : I × E→ℕ→ℂ := fun q n=>f q.1 q.2 n-g q.2 n
  have hterm (n : ℕ) : Tendsto (fun q : I × E=>F q n) (l ×ˢ 𝓟 Q) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.eventually_prod_principal_iff]
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hlim n)) ε hε] with t ht eta heta
    simpa only [F,dist_zero_right,←dist_eq_norm,dist_comm] using ht eta heta
  have henv : ∀ᶠq : I × E in l ×ˢ 𝓟 Q,∀n,‖F q n‖≤G n+G n := by
    rw [Filter.eventually_prod_principal_iff]
    filter_upwards [hbound] with t ht eta heta n
    exact (norm_sub_le _ _).trans (add_le_add (ht eta heta n) (hg eta heta n))
  have ht := tendsto_tsum_of_dominated_convergence (hG.add hG) hterm henv
  simp only [tsum_zero] at ht
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := (Metric.tendsto_nhds.mp ht) ε hε
  rw [Filter.eventually_prod_principal_iff] at he
  filter_upwards [he,hbound] with t ht hb eta heta
  have hsf : Summable (fun n=>f t eta n) := hG.of_norm_bounded (hb eta heta)
  have hsg : Summable (g eta) := hG.of_norm_bounded (hg eta heta)
  have hh := ht eta heta
  rw [dist_zero_right] at hh
  simpa only [F,hsf.tsum_sub hsg,←dist_eq_norm,dist_comm] using hh

/-- The common approaching envelope also bounds the boundary values, by the
actual uniform finite-term limits. -/
theorem uniform_tsum_of_common_approach_majorant {I E : Type*} {l : Filter I} [NeBot l]
    (f : I→E→ℕ→ℂ) (g : E→ℕ→ℂ) (Q : Set E) (G : ℕ→ℝ)
    (hG : Summable G)
    (hbound : ∀ᶠt in l,∀eta∈Q,∀n,‖f t eta n‖≤G n)
    (hlim : ∀n,TendstoUniformlyOn (fun t eta=>f t eta n) (fun eta=>g eta n) l Q) :
    TendstoUniformlyOn (fun t eta=>∑'n,f t eta n) (fun eta=>∑'n,g eta n) l Q := by
  apply uniform_tsum_of_common_majorant f g Q G hG _ hbound hlim
  intro eta heta n
  apply le_of_tendsto ((hlim n).tendsto_at heta).norm
  filter_upwards [hbound] with t ht
  exact ht eta heta n

/-- A common summable tail and genuinely uniform finite-term limits suffice;
the finitely many omitted particles are controlled on one common neighborhood. -/
theorem uniform_tsum_of_common_tail {I E : Type*} {l : Filter I} [NeBot l]
    (f : I→E→ℕ→ℂ) (g : E→ℕ→ℂ) (Q : Set E) (N : ℕ) (G H : ℕ→ℝ)
    (hH : Summable H) (hg : ∀eta∈Q,∀n,‖g eta n‖≤G n)
    (htail : ∀ᶠt in l,∀eta∈Q,∀k,‖f t eta (k+N)‖≤H k)
    (hlim : ∀n,TendstoUniformlyOn (fun t eta=>f t eta n) (fun eta=>g eta n) l Q) :
    TendstoUniformlyOn (fun t eta=>∑'n,f t eta n) (fun eta=>∑'n,g eta n) l Q := by
  let W : ℕ→ℝ := fun n=>if n<N then G n+1 else H (n-N)
  have hW : Summable W := by
    apply (summable_nat_add_iff N).mp
    convert hH using 1
    funext n
    simp only [W,ite_eq_right (show ¬n+N<N by omega),Nat.add_sub_cancel]
  have hfinite : ∀ᶠt in l,∀n∈Finset.range N,∀eta∈Q,dist (g eta n) (f t eta n)<1 := by
    apply (Filter.eventually_all_finset (Finset.range N)).mpr
    intro n _hn
    exact (Metric.tendstoUniformlyOn_iff.mp (hlim n)) 1 zero_lt_one
  apply uniform_tsum_of_common_approach_majorant f g Q W hW _ hlim
  filter_upwards [htail,hfinite] with t ht hf eta heta n
  by_cases hn : n<N
  · simp only [W,ite_eq_left hn]
    have hh := hf n (Finset.mem_range.mpr hn) eta heta
    rw [dist_eq_norm,norm_sub_rev] at hh
    have hnorm := norm_add_le (f t eta n-g eta n) (g eta n)
    rw [sub_add_cancel] at hnorm
    linarith [hg eta heta n]
  · simp only [W,ite_eq_right hn]
    have hh := ht eta heta (n-N)
    simpa only [Nat.sub_add_cancel (Nat.le_of_not_gt hn)] using hh

end
end IsingBulk.Joint.Negative
