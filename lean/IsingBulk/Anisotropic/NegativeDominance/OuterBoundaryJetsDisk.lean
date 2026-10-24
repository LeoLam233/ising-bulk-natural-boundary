import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryJetsAnalytic

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology BigOperators

theorem edgeComplexAmplitude_uniform_analytic {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) :
    ∀ᶠ u in 𝓝 (0:ℂ),∀N : ℕ,∀q : Fin N→ℝ,
      AnalyticAt ℂ (@edgeComplexAmplitude N b B S) (u,fun i=>(q i:ℂ)) ∧
      AnalyticAt ℂ (@edgeComplexDenominator N b B) (u,fun i=>(q i:ℂ)) := by
  have hden := radialEdgeRoot_denominator_uniform hb hB hBa.continuousAt
  have hden' := (continuousAt_id.prodMk (continuousAt_const (y := (1:ℝ)))).eventually hden
  filter_upwards [hBa.eventually_analyticAt,hSa.eventually_analyticAt,
    hSa.continuousAt.eventually_ne hS0,edgeParamW_uniform_domain hb hB hBa.continuousAt,hden']
    with u hu hSu hS0u hW hd
  intro N q
  apply edgeComplexAmplitude_analyticAt_of_domain hu hSu hS0u q
  · intro i
    simpa only [edgeParamW,cos_wrapAngle] using hW (wrapAngle (q i)) (wrapAngle_mem _)
  · intro i k
    have hh := hd (wrapAngle (q i)) (wrapAngle_mem _) (wrapAngle (q k)) (wrapAngle_mem _)
    simpa only [id_eq,radialEdgeRoot,edgeCircleRoot,radialEdgeY_one,edgeCircleW_unit,
      edgeParamRoot,edgeParamW,cos_wrapAngle] using hh

def outerComplexQuotient {N : ℕ} (b : ℝ) (B S f : ℂ→ℂ) (p : ℂ×(Fin N→ℂ)) : ℂ :=
  edgeComplexAmplitude b B S (f p.1,p.2)/edgeComplexDenominator b B (f p.1,p.2)

/-- One particle-scale disk of genuine joint holomorphy for the outer angular density. -/
theorem outerComplexQuotient_uniform_disk {b : ℝ} {B S f : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0)
    (κ : ℝ) (hκ : 0<κ) :
    ∃a : ℝ,0<a ∧ ∀N : ℕ,1≤N → ∀q : Fin N→ℝ,
      κ≤‖1-edgeRootProduct b B 0 q‖ → ∀u : ℂ,‖u‖<a/(N:ℝ) →
      AnalyticAt ℂ (@outerComplexQuotient N b B S f) (u,fun i=>(q i:ℂ)) ∧
      1-edgeRootProduct b B (f u) q≠0 := by
  obtain ⟨a,ha,hgap⟩ := edgeRootProduct_disk_of_boundary_gap hb hB hBa κ hκ
  obtain ⟨δ,hδ,hjoint⟩ := Metric.eventually_nhds_iff.mp
    (edgeComplexAmplitude_uniform_analytic hb hB hBa hSa hS0)
  obtain ⟨ε,L,hε,hL,hcoord⟩ := analytic_zero_uniform_linear_bound hf hf0
  let a' := min ε (min a δ/L)
  have ha' : 0<a' := lt_min hε (div_pos (lt_min ha hδ) hL)
  refine ⟨a',ha',?_⟩
  intro N hN q hboundary u hu
  have hNR : (1:ℝ)≤N := by exact_mod_cast hN
  have hNp : (0:ℝ)<N := by linarith
  have hscale : a'/(N:ℝ)≤a' := (div_le_iff₀ hNp).mpr (by nlinarith)
  have huε : ‖u‖<ε := hu.trans_le (hscale.trans (min_le_left _ _))
  obtain ⟨hfu,hfnorm⟩ := hcoord u huε
  have hLa : L*a'≤min a δ := by
    have hh := (le_div_iff₀ hL).mp (min_le_right ε (min a δ/L))
    nlinarith
  have hsmall : ‖f u‖<min a δ/(N:ℝ) := by
    have hh := mul_lt_mul_of_pos_left hu hL
    have hs := div_le_div_of_nonneg_right hLa hNp.le
    have he : L*(a'/(N:ℝ))=L*a'/(N:ℝ) := by ring
    rw [he] at hh
    exact hfnorm.trans_lt (hh.trans_le hs)
  have hfa : ‖f u‖<a/(N:ℝ) := hsmall.trans_le
    (div_le_div_of_nonneg_right (min_le_left _ _) hNp.le)
  have hfδ : ‖f u‖<δ := by
    have hh : min a δ/(N:ℝ)≤min a δ := (div_le_iff₀ hNp).mpr (by nlinarith [lt_min ha hδ])
    exact hsmall.trans_le (hh.trans (min_le_right _ _))
  have hwrapped : κ≤‖1-edgeRootProduct b B 0 (fun i=>wrapAngle (q i))‖ := by
    simpa only [edgeRootProduct,edgeParamRoot_wrapAngle] using hboundary
  have hg := (hgap N hN (fun i=>wrapAngle (q i)) (fun i=>wrapAngle_mem _) hwrapped (f u) hfa).2
  have hne : 1-edgeRootProduct b B (f u) q≠0 := by
    apply norm_pos_iff.mp
    have hh : 0<κ/2 := by positivity
    exact hh.trans_le (by simpa only [edgeRootProduct,edgeParamRoot_wrapAngle] using hg)
  have hj := hjoint (by simpa using hfδ) N q
  have hmap : AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ)=>(f p.1,p.2)) (u,fun i=>(q i:ℂ)) :=
    (hfu.comp analyticAt_fst).prod analyticAt_snd
  refine ⟨((hj.1.comp (f := fun p : ℂ×(Fin N→ℂ)=>(f p.1,p.2)) (x := (u,fun i=>(q i:ℂ))) hmap).div (hj.2.comp (f := fun p : ℂ×(Fin N→ℂ)=>(f p.1,p.2)) (x := (u,fun i=>(q i:ℂ))) hmap) ?_),hne⟩
  simpa only [edgeComplexDenominator,edgeComplexRoot_real,edgeRootProduct] using hne

end
end IsingBulk.Anisotropic.NegativeDominance
