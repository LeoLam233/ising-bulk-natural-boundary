import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace IsingBulk.Anisotropic
noncomputable section
open Set Filter
open scoped Topology

theorem analytic_eqOn_of_real_interval {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U)
    {a b : ℝ} (hab : a<b) (hi : ∀ x∈Ioo a b, (x:ℂ)∈U)
    (heq : ∀ x∈Ioo a b, f (x:ℂ)=g (x:ℂ)) : EqOn f g U := by
  let c := (a+b)/2
  have hac : a<c := by dsimp [c]; linarith
  have hcb : c<b := by dsimp [c]; linarith
  have ht : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] c) (𝓝[≠] (c:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa only [mem_compl_iff,mem_singleton_iff,Complex.ofReal_inj] using hx.ne'
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] c, x<b :=
    (eventually_lt_nhds hcb).filter_mono nhdsWithin_le_nhds
  have hfreq : ∃ᶠ x : ℝ in 𝓝[>] c, f (x:ℂ)=g (x:ℂ) := by
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin,hsmall] with x hx hxb
    exact heq x ⟨hac.trans hx,hxb⟩
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hU (hi c ⟨hac,hcb⟩)
    (ht.frequently hfreq)

end
end IsingBulk.Anisotropic
