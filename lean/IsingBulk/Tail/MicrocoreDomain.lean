import IsingBulk.Tail.MicrocoreLocalDensityJets
import IsingBulk.Tail.MicrocoreComplexChart
import Mathlib.Topology.Compactness.Compact

/-! Actual compact microcore centers generate a common open parameter domain. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie Filter Set
open scoped Topology ContDiff

def MicrocoreDensityPoint {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n) : Prop :=
  MicrocoreJetPoint v θ s x ∧ AnalyticAt ℂ microcoreVariableFactor (s,chartMap v θ s x) ∧
    1-regularZProduct s (chartMap v θ s x) ≠ 0

theorem microcoreDensityPoint_eventually {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (h : MicrocoreDensityPoint v θ s x) :
    ∀ᶠ z : ℂ × AngularSpace n in 𝓝 (s,x), MicrocoreDensityPoint v θ z.1 z.2 := by
  obtain ⟨hc,hchart⟩ := microcore_joint_chart_continuous v θ s x h.1
  have hfa : ∀ᶠ z : ℂ × AngularSpace n in 𝓝 (s,x),
      AnalyticAt ℂ microcoreVariableFactor (z.1,chartMap v θ z.1 z.2) :=
    hc.eventually h.2.1.eventually_analyticAt
  have hzc : ContinuousAt (fun z : ℂ × (Fin (n+1) → ℂ) => 1-regularZProduct z.1 z.2)
      (s,chartMap v θ s x) := by unfold regularZProduct; fun_prop
  have hza := (hzc.comp (f := fun z : ℂ × AngularSpace n => (z.1,chartMap v θ z.1 z.2)) hc).eventually_ne h.2.2
  filter_upwards [hchart,hfa,hza] with z hz hzf hzz
  exact ⟨hz,hzf,hzz⟩

theorem microcore_compact_parameter_domain {n : ℕ} (v θ : ℝ) (s : ℂ)
    (K : Set (AngularSpace n)) (hK : IsCompact K)
    (h : ∀ x ∈ K, MicrocoreDensityPoint v θ s x) :
    ∃ U : Set ℂ, IsOpen U ∧ s ∈ U ∧ ∀ t ∈ U, ∀ x ∈ K, MicrocoreDensityPoint v θ t x := by
  have he : ∀ᶠ t in 𝓝 s, ∀ x ∈ K, MicrocoreDensityPoint v θ t x :=
    hK.eventually_forall_of_forall_eventually (fun x hx => microcoreDensityPoint_eventually v θ s x (h x hx))
  obtain ⟨U,hU,hsub,hs⟩ := mem_nhds_iff.mp he
  exact ⟨U,hsub,hs,fun t ht => hU ht⟩

 theorem microcore_full_density_point_all_order {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w) (h : MicrocoreDensityPoint v θ s x) (j : ℕ) :
    ((lieStep (microcoreField v θ))^[j]
      (fun t y => (w y:ℂ)*chartPullback v θ (@microRegularDensity (n+1)) t y)) s x =
      microcoreTermSum v θ w (fun z : ℂ × (Fin (n+1) → ℂ) => microRegularDensity z.1 z.2) j s x := by
  have he := microcoreDensityPoint_eventually v θ s x h
  obtain ⟨U,R,hU,hs,hR,hx,hsub⟩ := mem_nhds_prod_iff'.mp he
  apply microcoreJetTerms_all_order v θ w (fun z : ℂ × (Fin (n+1) → ℂ) => microRegularDensity z.1 z.2)
    U R hU hR hw _ _ j s hs x hx
  · intro t ht y hy
    exact (hsub (show (t,y) ∈ U ×ˢ R from ⟨ht,hy⟩)).1
  · intro t ht y hy
    have hh := hsub (show (t,y) ∈ U ×ˢ R from ⟨ht,hy⟩)
    exact microRegularDensity_analytic _ hh.2.1 hh.2.2

end
end IsingBulk.Tail
