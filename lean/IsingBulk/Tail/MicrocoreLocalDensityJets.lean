import IsingBulk.Tail.MicrocoreDensityAllOrder
import IsingBulk.Tail.MicrocoreChartPoint

/-! A pointwise source chart generates its own open parameter/angular
neighborhood before all-order differentiation. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie IsingBulk.Branch Filter Set
open scoped Topology ContDiff

theorem microcore_joint_chart_continuous {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (h : MicrocoreJetPoint v θ s x) :
    ContinuousAt (fun z : ℂ × AngularSpace n => (z.1,chartMap v θ z.1 z.2)) (s,x) ∧
    ∀ᶠ z : ℂ × AngularSpace n in 𝓝 (s,x), MicrocoreJetPoint v θ z.1 z.2 := by
  have hW : ∀ i, ContinuousAt (fun z : ℂ × AngularSpace n => chartW z.1 v θ (z.2 i)) (s,x) := by
    intro i
    unfold chartW IsingBulk.Branch.dispersion angularY
    fun_prop (disch := first | exact h.s_ne | exact Complex.exp_ne_zero _)
  have hG : ∀ i, ContinuousAt (fun z : ℂ × AngularSpace n => angularG v θ (z.2 i)) (s,x) := by
    intro i
    unfold angularG angularY
    fun_prop (disch := exact Complex.exp_ne_zero _)
  have hphase : ContinuousAt (fun z : ℂ × AngularSpace n => chartMap v θ z.1 z.2) (s,x) := by
    apply continuousAt_pi.mpr
    intro i
    have hh := (lowerArccos_differentiable _ (h.re_pos i) (h.im_pos i)).continuousAt.comp
      (f := fun z : ℂ × AngularSpace n => chartW z.1 v θ (z.2 i)) (hW i)
    convert! hh using 1
  refine ⟨continuousAt_fst.prodMk hphase,?_⟩
  have hs := (show ContinuousAt (fun z : ℂ × AngularSpace n => z.1) (s,x) from continuousAt_fst).eventually_ne h.s_ne
  have hr := Filter.eventually_all.mpr (fun i => continuousAt_const.eventually_lt
    (Complex.continuous_re.continuousAt.comp (hW i)) (h.re_pos i))
  have hi := Filter.eventually_all.mpr (fun i => continuousAt_const.eventually_lt
    (Complex.continuous_im.continuousAt.comp (hW i)) (h.im_pos i))
  have hg := Filter.eventually_all.mpr (fun i => continuousAt_const.eventually_lt
    (Complex.continuous_re.continuousAt.comp (hG i)) (h.g_pos i))
  filter_upwards [hs,hr,hi,hg] with z hzs hzr hzi hzg
  exact microcoreJetPoint_of_quadrants v θ z.1 z.2 hzs hzr hzi hzg

theorem microcore_density_point_all_order {n : ℕ} (v θ : ℝ) (s : ℂ) (x : AngularSpace n)
    (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w) (h : MicrocoreJetPoint v θ s x)
    (hF : AnalyticAt ℂ microcoreVariableFactor (s,chartMap v θ s x))
    (hZ : 1-regularZProduct s (chartMap v θ s x) ≠ 0) (j : ℕ) :
    ((lieStep (microcoreField v θ))^[j]
      (fun t y => (w y:ℂ)*chartPullback v θ (@microRegularDensity (n+1)) t y)) s x =
      microcorePhaseFactor (chartMap v θ s x)*microcoreTermSum v θ w microcoreVariableFactor j s x := by
  obtain ⟨hcont,hchart⟩ := microcore_joint_chart_continuous v θ s x h
  have hfa : ∀ᶠ z : ℂ × AngularSpace n in 𝓝 (s,x), AnalyticAt ℂ microcoreVariableFactor (z.1,chartMap v θ z.1 z.2) := hcont.eventually hF.eventually_analyticAt
  have hzc : ContinuousAt (fun z : ℂ × (Fin (n+1) → ℂ) => 1-regularZProduct z.1 z.2)
      (s,chartMap v θ s x) := by unfold regularZProduct; fun_prop
  have hza :=  (hzc.comp (f := fun z : ℂ × AngularSpace n => (z.1,chartMap v θ z.1 z.2)) hcont).eventually_ne hZ
  have he : {z : ℂ × AngularSpace n | MicrocoreJetPoint v θ z.1 z.2 ∧
      AnalyticAt ℂ microcoreVariableFactor (z.1,chartMap v θ z.1 z.2) ∧
      1-regularZProduct z.1 (chartMap v θ z.1 z.2) ≠ 0} ∈ 𝓝 (s,x) := by
    filter_upwards [hchart,hfa,hza] with z hz hzf hzz
    exact ⟨hz,hzf,hzz⟩
  obtain ⟨U,R,hU,hs,hR,hx,hsub⟩ := mem_nhds_prod_iff'.mp he
  apply microcore_density_all_order v θ w U R hU hR hw _ _ _ j s hs x hx
  · intro t ht y hy
    exact (hsub (show (t,y) ∈ U ×ˢ R from ⟨ht,hy⟩)).1
  · intro t ht y hy
    exact (hsub (show (t,y) ∈ U ×ˢ R from ⟨ht,hy⟩)).2.1
  · intro t ht y hy
    exact (hsub (show (t,y) ∈ U ×ˢ R from ⟨ht,hy⟩)).2.2

end
end IsingBulk.Tail
