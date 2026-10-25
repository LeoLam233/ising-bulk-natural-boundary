import IsingBulk.Joint.RegularEdges.FamilyFiniteAnalytic

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric MeasureTheory IsingBulk.First IsingBulk.Tail
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def familyAngularJet {N : ℕ} (b : ℝ) (B S : ℂ × E → ℂ) (j : ℕ)
    (p : ℂ × (E × (Fin N → ℝ))) : ℂ :=
  iteratedDeriv j (fun u => edgeAngularDensity b (fun u=>B (u,p.2.1))
    (fun u=>S (u,p.2.1)) u p.2.2) p.1

theorem familyAngularJet_continuousAt {N : ℕ} {b : ℝ} {B S : ℂ × E → ℂ}
    {eta : E} (hb : |b|<1) (hB : AnalyticAt ℂ B (0,eta)) (hBi : 0<(B (0,eta)).im)
    (hS : AnalyticAt ℂ S (0,eta)) (hS0 : S (0,eta)≠0) (q : Fin N→ℝ)
    (hne : edgeRootProduct b (fun u=>B (u,eta)) 0 q≠1) (j : ℕ) :
    ContinuousAt (familyAngularJet (N:=N) b B S j) (0,(eta,q)) := by
  let G : ℂ × (E × (Fin N→ℝ)) → ℂ × (E × (Fin N→ℂ)) :=
    fun p => (p.1,(p.2.1,fun i => (p.2.2 i:ℂ)))
  have hG : Continuous G := by unfold G; fun_prop
  have hA := familyEdgeAmplitude_analyticAt_real hb hB hBi hS hS0 q
  have hD := familyEdgeDenominator_analyticAt_real hb hB hBi q
  have hJ := familyEdgeJet_analyticAt_real hb hB hBi hS hS0 q j
  have hn : familyEdgeDenominator b B (G (0,(eta,q)))≠0 := by
    simpa [G,familyEdgeDenominator,edgeComplexDenominator,edgeRootProduct,sub_ne_zero]
      using hne.symm
  let F : ℂ × (E × (Fin N→ℝ)) → ℂ := fun p =>
    (firstVandermonde p.2.2:ℂ)^2*edgeSincFactor p.2.2*familyEdgeJet b B S j (G p)/
      familyEdgeDenominator b B (G p)^(j+1)
  have hFc : ContinuousAt F (0,(eta,q)) := by
    apply ContinuousAt.div
    · apply ContinuousAt.mul
      · exact ((by unfold firstVandermonde; fun_prop :
          Continuous (fun p : ℂ × (E × (Fin N→ℝ)) => (firstVandermonde p.2.2:ℂ)^2)).continuousAt).mul
          ((edgeSincFactor_continuous N).continuousAt.comp (continuousAt_snd.comp continuousAt_snd))
      · exact hJ.continuousAt.comp (f:=G) (x:=(0,(eta,q))) hG.continuousAt
    · exact (hD.continuousAt.comp (f:=G) (x:=(0,(eta,q))) hG.continuousAt).pow _
    · exact pow_ne_zero _ hn
  have hneEv := (hD.continuousAt.comp (f:=G) (x:=(0,(eta,q))) hG.continuousAt).eventually_ne hn
  have heq : familyAngularJet b B S j =ᶠ[𝓝 (0,(eta,q))] F := by
    filter_upwards [(hG.tendsto (0,(eta,q))).eventually hA.eventually_analyticAt,
      (hG.tendsto (0,(eta,q))).eventually hD.eventually_analyticAt,hneEv] with p ha hd hp
    have hu : AnalyticAt ℂ (fun u : ℂ => (u,(p.2.1,fun i => (p.2.2 i:ℂ)))) p.1 :=
      analyticAt_id.prod analyticAt_const
    exact edgeAngularDensity_iteratedDeriv b (fun u=>B (u,p.2.1)) (fun u=>S (u,p.2.1)) p.2.2 p.1 j
      (ha.comp (f:=fun u : ℂ => (u,(p.2.1,fun i => (p.2.2 i:ℂ)))) hu)
      (hd.comp (f:=fun u : ℂ => (u,(p.2.1,fun i => (p.2.2 i:ℂ)))) hu) hp
  exact hFc.congr_of_eventuallyEq heq

/-- Actual family jets have one common complex neighborhood on every compact
angular set without a lattice pole. -/
theorem compact_family_constrained_jet_bound {n : ℕ} {b : ℝ} (B S : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    {L : Set (Fin n→ℝ)} (hL : IsCompact L)
    (hne : ∀eta∈Q,∀q∈L,edgeRootProduct b (fun u=>B (u,eta)) 0 (shapeExtend q)≠1) (j : ℕ) :
    ∃ δ C : ℝ,0<δ ∧ 0<C ∧ ∀eta∈Q,∀u : ℂ,‖u‖<δ → ∀q∈L,
      ‖edgeConstrainedJet b (fun u=>B (u,eta)) (fun u=>S (u,eta)) j (u,q)‖≤C := by
  let F : ℂ × (E × (Fin n→ℝ)) → ℂ := fun p =>
    edgeConstrainedJet b (fun u=>B (u,p.2.1)) (fun u=>S (u,p.2.1)) j (p.1,p.2.2)
  have hc (v : E × (Fin n→ℝ)) (hv : v∈Q ×ˢ L) : ContinuousAt F (0,v) := by
    exact (familyAngularJet_continuousAt hb (hB v.1 hv.1) (hBi v.1 hv.1)
      (hS v.1 hv.1) (hS0 v.1 hv.1) (shapeExtend v.2) (hne v.1 hv.1 v.2 hv.2) j).comp
        (f:=fun p : ℂ × (E × (Fin n→ℝ)) => (p.1,(p.2.1,shapeExtend p.2.2))) (x:=(0,v))
        (by unfold shapeExtend; fun_prop)
  have hcont : ContinuousOn (fun v => F (0,v)) (Q ×ˢ L) := by
    intro v hv
    exact ((hc v hv).comp (f:=fun v => ((0:ℂ),v))
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  obtain ⟨M,hM⟩ := (hQ.prod hL).exists_bound_of_continuousOn hcont
  have he : ∀ᶠu : ℂ in 𝓝 0,∀v∈Q ×ˢ L,‖F (u,v)‖<max M 0+1 := by
    apply (hQ.prod hL).eventually_forall_of_forall_eventually
    intro v hv
    exact (hc v hv).norm.eventually_lt continuousAt_const
      ((hM v hv).trans_lt (by linarith [le_max_left M 0]))
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨δ,max M 0+1,hδ,by positivity,fun eta heta u hu q hq =>
    (hδb (by simpa using hu) (eta,q) ⟨heta,hq⟩).le⟩

/-- Uniform finite lower nonresonant derivatives of the COMPLETE angular integral. -/
theorem compact_family_nonresonant_integral_bound {n : ℕ} {b : ℝ} (B S : ℂ × E → ℂ)
    (hb : |b|<1) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hBi : ∀eta∈Q,0<(B (0,eta)).im)
    (hS : ∀eta∈Q,AnalyticAt ℂ S (0,eta)) (hS0 : ∀eta∈Q,S (0,eta)≠0)
    (hres : continuedRoot (b:ℂ)^(n+1)≠1) (j : ℕ) :
    ∃ δ C : ℝ,0<δ ∧ 0≤C ∧ ∀eta∈Q,∀u : ℂ,‖u‖<δ →
      ‖edgeFullDerivativeIntegral (n:=n) b (fun u=>B (u,eta)) (fun u=>S (u,eta)) j u‖≤C := by
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_family_constrained_jet_bound B S hb hQ hB hBi hS hS0
    (L:=edgeCenteredCube n) isCompact_Icc
    (fun eta heta q hq h => hres ((edgeRootProduct_constrained_eq_one_iff hb (hBi eta heta) q
      (fun i=>⟨hq.1 i,hq.2 i⟩)).mp h).2) j
  refine ⟨δ,C*volume.real (edgeCenteredCube n),hδ,by positivity,?_⟩
  intro eta heta u hu
  apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
  exact fun q hq => hbound eta heta u hu q hq

end
end IsingBulk.Joint.RegularEdges
