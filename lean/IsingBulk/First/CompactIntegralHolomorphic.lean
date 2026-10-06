import IsingBulk.First.CompactAnalyticShapeIntegral
import IsingBulk.First.CompactJetIntegral

/-! Holomorphy of genuine compact parameter integrals, with the fixed
continuous shape weight kept outside the analytic family. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

theorem compact_joint_jet_integral_analyticAt
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {U : Set ℂ} (hU : IsOpen U) (H : ℕ → ℂ → X → ℂ)
    (hc : ∀ j, ContinuousOn (fun p : ℂ × X => H j p.1 p.2) (U ×ˢ K))
    (hd : ∀ j s, s ∈ U → ∀ x ∈ K, HasDerivAt (fun z => H j z x) (H (j+1) s x) s)
    {s : ℂ} (hs : s ∈ U) : AnalyticAt ℂ (fun z => ∫ x in K, H 0 z x ∂μ) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [hU.mem_nhds hs] with z hz
  exact (hasDerivAt_compact_integral hK (hU.mem_nhds hz) (H 0) (H 1) (hc 0) (hc 1) (hd 0)).differentiableAt

theorem compact_analytic_shape_integral_analyticAt
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ × E → ℂ) (psi : X → E) (hpsi : Continuous psi)
    (chi : X → ℂ) (hchi : Continuous chi)
    (hF : ∀ s ∈ U, ∀ x ∈ K, AnalyticAt ℂ F (s,psi x)) {s : ℂ} (hs : s ∈ U) :
    AnalyticAt ℂ (fun z => ∫ x in K, chi x*F (z,psi x) ∂μ) s := by
  let H := fun j z x => chi x*jointParameterJet F j (z,psi x)
  have hc (j : ℕ) : ContinuousOn (fun p : ℂ × X => H j p.1 p.2) (U ×ˢ K) := by
    intro p hp
    have hcomp : ContinuousAt (fun q : ℂ × X => jointParameterJet F j (q.1,psi q.2)) p :=
      (jointParameterJet_analyticAt (hF p.1 hp.1 p.2 hp.2) j).continuousAt.comp
        (f := fun q : ℂ × X => (q.1,psi q.2))
        (continuous_fst.prodMk (hpsi.comp continuous_snd)).continuousAt
    exact (((hchi.comp continuous_snd).continuousAt).mul hcomp).continuousWithinAt
  have hd (j : ℕ) (z : ℂ) (hz : z ∈ U) (x : X) (hx : x ∈ K) :
      HasDerivAt (fun w => H j w x) (H (j+1) z x) z := by
    have ha := (jointParameterJet_analyticAt (hF z hz x hx) j).comp
      (f := fun w : ℂ => (w,psi x)) (analyticAt_id.prod analyticAt_const)
    convert ha.differentiableAt.hasDerivAt.const_mul (chi x) using 1 <;>
      simp only [H,jointParameterJet,Function.iterate_succ',Function.comp_def,parameterDeriv]
  exact compact_joint_jet_integral_analyticAt hK hU H hc hd hs

end
end IsingBulk.First
