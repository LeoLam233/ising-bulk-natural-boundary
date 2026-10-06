import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic

/-! Quadratic limits of actual analytic germs, with an explicitly proved
Taylor remainder. This is used for each fixed constrained shape after mean residue. -/
namespace IsingBulk.First
noncomputable section
open Set Filter
open scoped Topology

theorem analytic_quadratic_quotient_limit {f : ℂ → ℂ} {q : ℂ}
    (ha : AnalyticAt ℂ f 0) (h0 : f 0 = 0) (h1 : deriv f 0 = 0)
    (h2 : deriv (deriv f) 0 = 2*q) :
    Tendsto (fun z : ℂ => f z/z^2) (𝓝[≠] 0) (𝓝 q) := by
  obtain ⟨g, hg, he⟩ := ha.exists_eventuallyEq_sum_add_pow_mul 3
  have hi2 : iteratedDeriv 2 f 0 = 2*q := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using h2
  have hpoly (z : ℂ) :
      (∑ i ∈ Finset.range 3, (z^i/(i.factorial : ℂ)) • iteratedDeriv i f 0) = z^2*q := by
    simp [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, h0, h1, hi2]
    ring
  have ht : Tendsto (fun z : ℂ => q+z*g z) (𝓝 0) (𝓝 q) := by
    simpa using tendsto_const_nhds.add (tendsto_id.mul hg.continuousAt.tendsto)
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hne
  rw [hz, hpoly]
  have hn : z ≠ 0 := by simpa using hne
  simp only [smul_eq_mul]
  field_simp

theorem analytic_quadratic_quotient_limit_real {f : ℂ → ℂ} {q : ℂ}
    (ha : AnalyticAt ℂ f 0) (h0 : f 0 = 0) (h1 : deriv f 0 = 0)
    (h2 : deriv (deriv f) 0 = 2*q) :
    Tendsto (fun lam : ℝ => f (lam:ℂ)/(lam:ℂ)^2) (𝓝[>] 0) (𝓝 q) := by
  have ht : Tendsto (fun lam : ℝ => (lam : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with lam hlam
      simpa using Complex.ofReal_ne_zero.mpr (Set.mem_Ioi.mp hlam).ne'
  exact (analytic_quadratic_quotient_limit ha h0 h1 h2).comp ht

end
end IsingBulk.First
