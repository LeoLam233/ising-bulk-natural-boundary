import IsingBulk.Joint.Negative.CompactAnalyticBounds

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Analytic uniqueness makes natural fiber identities hold on one common
complex disk. No uniform identity radius is requested as a premise. -/
theorem compact_family_analytic_identity (f g : ℂ × E→ℂ) {Q : Set E}
    (hQ : IsCompact Q) (hf : ∀eta∈Q,AnalyticAt ℂ f (0,eta))
    (hg : ∀eta∈Q,AnalyticAt ℂ g (0,eta))
    (he : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,f (t,eta)=g (t,eta)) :
    ∃r : ℝ,0<r ∧ ∀eta∈Q,∀t : ℂ,‖t‖<r → f (t,eta)=g (t,eta) := by
  obtain ⟨a,A,ha,_hA,hfa⟩ := compact_analytic_uniform_bound f hQ hf
  obtain ⟨b,B,hb,_hB,hga⟩ := compact_analytic_uniform_bound g hQ hg
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro eta heta
  have hfd : AnalyticOnNhd ℂ (fun t : ℂ=>f (t,eta)) (ball 0 (min a b)) := by
    intro t ht
    exact (hfa eta heta t ((mem_ball_zero_iff.mp ht).trans_le (min_le_left _ _))).1.comp
      (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  have hgd : AnalyticOnNhd ℂ (fun t : ℂ=>g (t,eta)) (ball 0 (min a b)) := by
    intro t ht
    exact (hga eta heta t ((mem_ball_zero_iff.mp ht).trans_le (min_le_right _ _))).1.comp
      (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  have hh := hfd.eqOn_of_preconnected_of_eventuallyEq hgd (convex_ball (0:ℂ) (min a b)).isPreconnected
    (mem_ball_self (lt_min ha hb)) (he eta heta)
  exact fun t ht=>hh (mem_ball_zero_iff.mpr ht)

end
end IsingBulk.Joint.Negative
