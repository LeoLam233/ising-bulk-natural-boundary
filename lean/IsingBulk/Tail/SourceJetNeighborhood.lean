import IsingBulk.Tail.SourceJetIntegralTheorem
import IsingBulk.Tail.AllBranchExteriorPoint

/-! Genuine center chart data generates its own open neighborhoods for the
frozen source jet compiler; no open-chart hypothesis is left to the caller. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie IsingBulk.Branch Set Filter Function
open scoped Topology ContDiff
set_option maxHeartbeats 1000000

theorem coefficientPoint_eventually {N : ℕ} (p q : Fin N) (z : ℂ × (Fin N → ℂ))
    (h : CoefficientPoint p q z) : ∀ᶠ t in 𝓝 z,CoefficientPoint p q t := by
  have hc (i : Fin N) : ContinuousAt (fun t : ℂ × (Fin N → ℂ) => (t.1,t.2 i)) z := by fun_prop
  have hpair : ContinuousAt (fun t : ℂ × (Fin N → ℂ) => (t.1,t.2 p,t.2 q)) z := by fun_prop
  have ha := Filter.eventually_all.mpr (fun i => (hc i).eventually (h.a i).eventually_analyticAt)
  have hg := Filter.eventually_all.mpr (fun i => (hc i).eventually (h.g i).eventually_analyticAt)
  have hd := hpair.eventually h.den.eventually_analyticAt
  have hdn := h.continuity.2.eventually_ne h.den_ne
  have hgn := h.continuity.1.eventually_ne h.gsum_ne
  filter_upwards [ha,hg,hd,hdn,hgn] with t hta htg htd htdn htgn
  exact ⟨hta,htg,htd,htdn,htgn⟩

theorem actualJetPoint_eventually_original {n : ℕ} (v theta : ℝ) (p q : Fin (n+1))
    (s : ℂ) (x : AngularSpace n) (hv : v < 0) (h : ActualJetPoint v theta p q s x) :
    ∀ᶠ z : ℂ × AngularSpace n in 𝓝 (s,x), ActualJetPoint v theta p q z.1 z.2 := by
  let hM : MicrocoreJetPoint v theta s x := ⟨h.s_ne,h.re_pos,h.im_pos,h.g_pos,h.sin_ne,h.slit⟩
  obtain ⟨hc,hm⟩ := microcore_joint_chart_continuous v theta s x hM
  have hcoeff := hc.eventually (coefficientPoint_eventually p q _ h.coefficient)
  have hdc : ContinuousAt (fun z : ℂ × AngularSpace n =>
      chartMap v theta z.1 z.2 q-chartMap v theta z.1 z.2 p) (s,x) :=
    ((continuous_apply q).continuousAt.comp hc.snd).sub
      ((continuous_apply p).continuousAt.comp hc.snd)
  have hdelta := hdc.eventually_ne h.delta_ne
  filter_upwards [hm,hcoeff,hdelta] with z hzm hzc hzd
  exact allBranchExterior_actualJetPoint_of_micro v theta z.1 z.2 p q hv hzm hzc hzd

theorem sourceJetTerms_all_order_analytic {n : ℕ} (p q : Fin (n+1)) (hpq : p≠q)
    (v theta : ℝ) (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (U : Set ℂ) (R : Set (AngularSpace n))
    (hU : IsOpen U) (hR : IsOpen R)
    (hpoint : ∀ s∈U,∀ x∈R,ActualJetPoint v theta p q s x)
    (hQ : ∀ s∈U,∀ x∈R,AnalyticAt ℂ Q (s,chartMap v theta s x)) (j : ℕ) :
    ∀ s∈U,∀ x∈R,
      ((lieStep (actualField v theta p q))^[j] (initialSourceDensity v theta w Q)) s x =
        sourceTermSum p q v theta w Q j s x := by
  induction j with
  | zero => intro s hs x hx; rw [sourceTermSum_zero]; rfl
  | succ j ih =>
    intro s hs x hx
    rw [Function.iterate_succ_apply',lieStep_congr_on (actualField v theta p q) hU hR ih hs hx]
    exact sourceTermSum_step p q hpq v theta w Q j s x hw (hpoint s hs x hx) (hQ s hs x hx)

theorem source_point_all_order {n : ℕ} (v theta : ℝ) (p q : Fin (n+1)) (hpq : p≠q)
    (s : ℂ) (x : AngularSpace n) (hv : v < 0) (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (hpoint : ActualJetPoint v theta p q s x)
    (hQ : AnalyticAt ℂ Q (s,chartMap v theta s x)) (j : ℕ) :
    ((lieStep (actualField v theta p q))^[j] (initialSourceDensity v theta w Q)) s x =
      sourceTermSum p q v theta w Q j s x := by
  have hc := (microcore_joint_chart_continuous v theta s x
    ⟨hpoint.s_ne,hpoint.re_pos,hpoint.im_pos,hpoint.g_pos,hpoint.sin_ne,hpoint.slit⟩).1
  have he := (actualJetPoint_eventually_original v theta p q s x hv hpoint).and (hc.eventually hQ.eventually_analyticAt)
  obtain ⟨U,R,hU,hs,hR,hx,hsub⟩ := mem_nhds_prod_iff'.mp he
  exact sourceJetTerms_all_order_analytic p q hpq v theta w hw Q U R hU hR
    (fun t ht y hy => (hsub (show (t,y)∈U×ˢR from ⟨ht,hy⟩)).1)
    (fun t ht y hy => (hsub (show (t,y)∈U×ˢR from ⟨ht,hy⟩)).2) j s hs x hx

end
end IsingBulk.Tail
