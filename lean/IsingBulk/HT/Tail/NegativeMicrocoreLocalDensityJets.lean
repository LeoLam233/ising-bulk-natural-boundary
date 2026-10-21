import IsingBulk.HT.Tail.NegativeMicrocoreFactors
import IsingBulk.Tail.MicrocoreLocalDensityJets
import IsingBulk.Tail.MicrocoreDensityAllOrder
import IsingBulk.Tail.MicrocoreChartPoint

/-! A pointwise source chart generates its own open parameter/angular
neighborhood before all-order differentiation. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.Tail IsingBulk.HT.Contour
open IsingBulk.Jets IsingBulk.Lie IsingBulk.Branch Filter Set
open scoped Topology ContDiff

theorem negative_microcore_density_point_all_order {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w) (h : MicrocoreJetPoint v θ s x)
    (hF : AnalyticAt ℂ negativeMicrocoreVariableFactor (s,chartMap v θ s x))
    (hZ : 1+regularZProduct s (chartMap v θ s x) ≠ 0) (j : ℕ) :
    ((lieStep (microcoreField v θ))^[j]
      (fun t y => (w y:ℂ)*chartPullback v θ (@negativeMicroRegularDensity (n+1)) t y)) s x =
      negativeMicrocorePhaseFactor (chartMap v θ s x)*microcoreTermSum v θ w negativeMicrocoreVariableFactor j s x := by
  obtain ⟨hcont,hchart⟩ := microcore_joint_chart_continuous v θ s x h
  have hfa : ∀ᶠ z : ℂ × AngularSpace n in 𝓝 (s,x), AnalyticAt ℂ negativeMicrocoreVariableFactor (z.1,chartMap v θ z.1 z.2) := hcont.eventually hF.eventually_analyticAt
  have hzc : ContinuousAt (fun z : ℂ × (Fin (n+1) → ℂ) => 1+regularZProduct z.1 z.2)
      (s,chartMap v θ s x) := by unfold regularZProduct; fun_prop
  have hza :=  (hzc.comp (f := fun z : ℂ × AngularSpace n => (z.1,chartMap v θ z.1 z.2)) hcont).eventually_ne hZ
  have he : {z : ℂ × AngularSpace n | MicrocoreJetPoint v θ z.1 z.2 ∧
      AnalyticAt ℂ negativeMicrocoreVariableFactor (z.1,chartMap v θ z.1 z.2) ∧
      1+regularZProduct z.1 (chartMap v θ z.1 z.2) ≠ 0} ∈ 𝓝 (s,x) := by
    filter_upwards [hchart,hfa,hza] with z hz hzf hzz
    exact ⟨hz,hzf,hzz⟩
  obtain ⟨U,R,hU,hs,hR,hx,hsub⟩ := mem_nhds_prod_iff'.mp he
  apply negative_microcore_density_all_order v θ w U R hU hR hw _ _ _ j s hs x hx
  · intro t ht y hy
    exact (hsub (show (t,y) ∈ U ×ˢ R from ⟨ht,hy⟩)).1
  · intro t ht y hy
    exact (hsub (show (t,y) ∈ U ×ˢ R from ⟨ht,hy⟩)).2.1
  · intro t ht y hy
    exact (hsub (show (t,y) ∈ U ×ˢ R from ⟨ht,hy⟩)).2.2

end
end IsingBulk.HT.Tail
