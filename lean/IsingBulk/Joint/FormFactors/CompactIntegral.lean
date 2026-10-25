import IsingBulk.First.CompactParameterIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Fréchet differentiation of genuine compact integrals with independent complex
parameters. This is not separate analyticity along the positive-ratio lines. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

variable {E V G X : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]

omit [CompleteSpace G] in
theorem hasFDerivAt_compact_integral {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    {K : Set X} (hK : IsCompact K) {U : Set E} {s : E} (hU : U ∈ 𝓝 s)
    (F : E → X → G) (DF : E → X → E →L[ℂ] G)
    (hF : ContinuousOn (fun p : E × X => F p.1 p.2) (U ×ˢ K))
    (hDF : ContinuousOn (fun p : E × X => DF p.1 p.2) (U ×ˢ K))
    (hd : ∀ t ∈ U, ∀ a ∈ K, HasFDerivAt (fun z => F z a) (DF t a) t) :
    HasFDerivAt (fun t => ∫ a in K, F t a ∂μ) (∫ a in K, DF s a ∂μ) s := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hsU := mem_of_mem_nhds hU
  have hball : closedBall s (ε/2) ⊆ U :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  have hFc (t : E) (ht : t ∈ U) : ContinuousOn (F t) K :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ha => ⟨ht, ha⟩)
  have hDc (t : E) (ht : t ∈ U) : ContinuousOn (DF t) K :=
    hDF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ha => ⟨ht, ha⟩)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s (ε/2)).prod hK).exists_bound_of_continuousOn
    (hDF.mono (prod_mono hball Subset.rfl))
  have hbound : Integrable (fun _a : X => C) (μ.restrict K) :=
    integrableOn_const hK.measure_lt_top.ne
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (closedBall_mem_nhds s (by linarith : 0 < ε/2))
    ((Filter.Eventually.mono hU) (fun t ht => ((hFc t ht).integrableOn_compact hK).aestronglyMeasurable))
    ((hFc s hsU).integrableOn_compact hK)
    ((hDc s hsU).integrableOn_compact hK).aestronglyMeasurable
    ?_ hbound ?_
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro t ht
    exact hC (t,a) ⟨ht,ha⟩
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro t ht
    exact hd t (hball ht) a ha

def parameterFDeriv (F : E × V → G) (p : E × V) : E →L[ℂ] G :=
  (fderiv ℂ F p).comp (ContinuousLinearMap.inl ℂ E V)

omit [ProperSpace E] in
theorem parameterFDeriv_analyticAt {F : E × V → G} {p : E × V}
    (hF : AnalyticAt ℂ F p) : AnalyticAt ℂ (parameterFDeriv F) p := by
  let L := (ContinuousLinearMap.compL ℂ E (E × V) G).flip
    (ContinuousLinearMap.inl ℂ E V)
  exact (L.analyticAt _).comp hF.fderiv

theorem compact_analytic_integral_hasFDerivAt
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {U : Set E} (hU : IsOpen U) (F : E × V → G) (psi : X → V) (hpsi : Continuous psi)
    (hF : ∀ s ∈ U, ∀ x ∈ K, AnalyticAt ℂ F (s,psi x)) {s : E} (hs : s ∈ U) :
    HasFDerivAt (fun z => ∫ x in K, F (z,psi x) ∂μ)
      (∫ x in K, parameterFDeriv F (s,psi x) ∂μ) s := by
  have hc : ContinuousOn (fun p : E × X => F (p.1,psi p.2)) (U ×ˢ K) := by
    intro p hp
    exact ((hF p.1 hp.1 p.2 hp.2).continuousAt.comp (f := fun q : E × X => (q.1,psi q.2))
      (continuous_fst.prodMk (hpsi.comp continuous_snd)).continuousAt).continuousWithinAt
  have hdc : ContinuousOn (fun p : E × X => parameterFDeriv F (p.1,psi p.2)) (U ×ˢ K) := by
    intro p hp
    exact ((parameterFDeriv_analyticAt (hF p.1 hp.1 p.2 hp.2)).continuousAt.comp (f := fun q : E × X => (q.1,psi q.2))
      (continuous_fst.prodMk (hpsi.comp continuous_snd)).continuousAt).continuousWithinAt
  apply hasFDerivAt_compact_integral hK (hU.mem_nhds hs) _ _ hc hdc
  intro z hz x hx
  exact (hF z hz x hx).differentiableAt.hasFDerivAt.comp z
    ((hasFDerivAt_id z).prodMk (hasFDerivAt_const (psi x) z))

/-- Every finite Fréchet derivative exists for the compact integral. The induction
uses the actual parameter derivative of the integrand, never a jet oracle. -/
theorem compact_analytic_integral_contDiffAt (n : ℕ)
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {U : Set E} (hU : IsOpen U) (F : E × V → G) (psi : X → V) (hpsi : Continuous psi)
    (hF : ∀ s ∈ U, ∀ x ∈ K, AnalyticAt ℂ F (s,psi x)) {s : E} (hs : s ∈ U) :
    ContDiffAt ℂ n (fun z => ∫ x in K, F (z,psi x) ∂μ) s := by
  induction n generalizing G with
  | zero =>
    exact contDiffAt_zero.mpr ⟨U,hU.mem_nhds hs, fun z hz =>
      (compact_analytic_integral_hasFDerivAt (μ := μ) hK hU F psi hpsi hF hz).continuousAt.continuousWithinAt⟩
  | succ n ih =>
    rw [show ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 from rfl,
      contDiffAt_succ_iff_hasFDerivAt]
    refine ⟨fun z => ∫ x in K, parameterFDeriv F (z,psi x) ∂μ, ?_, ?_⟩
    · exact ⟨U, hU.mem_nhds hs, fun z hz =>
        compact_analytic_integral_hasFDerivAt hK hU F psi hpsi hF hz⟩
    · exact ih (parameterFDeriv F) (fun z hz x hx => parameterFDeriv_analyticAt (hF z hz x hx))

theorem compact_analytic_shape_integral_contDiffAt (n : ℕ)
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {U : Set E} (hU : IsOpen U) (F : E × V → G) (psi : X → V) (hpsi : Continuous psi)
    (chi : X → ℂ) (hchi : Continuous chi)
    (hF : ∀ s ∈ U, ∀ x ∈ K, AnalyticAt ℂ F (s,psi x)) {s : E} (hs : s ∈ U) :
    ContDiffAt ℂ n (fun z => ∫ x in K, chi x • F (z,psi x) ∂μ) s := by
  let F' : E × (V × ℂ) → G := fun q => q.2.2 • F (q.1,q.2.1)
  have ha : ∀ z ∈ U, ∀ x ∈ K, AnalyticAt ℂ F' (z,(psi x,chi x)) := by
    intro z hz x hx
    have hmap : AnalyticAt ℂ (fun q : E × (V × ℂ) => (q.1,q.2.1))
        (z,(psi x,chi x)) :=
      analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
    have hcomp := (hF z hz x hx).comp (f := fun q : E × (V × ℂ) => (q.1,q.2.1)) hmap
    exact (analyticAt_snd.comp analyticAt_snd).smul hcomp
  exact compact_analytic_integral_contDiffAt n hK hU F'
    (fun x => (psi x,chi x)) (hpsi.prodMk hchi) ha hs

end
end IsingBulk.Joint.FormFactors
