import IsingBulk.Anisotropic.RegularEdges.LeadingJets
import IsingBulk.Anisotropic.RegularEdges.LeadingScaling

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter
open scoped Topology BigOperators

theorem edgeComplexRoot_joint_analyticAt_real {N : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (q : Fin N→ℝ) (i : Fin N) :
    AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => edgeComplexRoot b B p.1 (p.2 i))
      (0,fun k => (q k:ℂ)) := by
  have dq : AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => p.2 i) (0,fun k => (q k:ℂ)) :=
    (ContinuousLinearMap.proj i : (Fin N→ℂ)→L[ℂ] ℂ).analyticAt _ |>.comp analyticAt_snd
  have dB : AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => B p.1) (0,fun k => (q k:ℂ)) :=
    hB.comp (x := ((0,fun k => (q k:ℂ)):ℂ×(Fin N→ℂ))) analyticAt_fst
  exact AnalyticAt.fun_comp_of_eq
    (f := fun p : ℂ×(Fin N→ℂ) => (b:ℂ)+p.1+B p.1*(1-Complex.cos (p.2 i)))
    (g := continuedRoot) (continuedRoot_analyticAt (edgeW_domain hb hBi (q i)))
    ((analyticAt_const.add analyticAt_fst).add
      (dB.mul (analyticAt_const.sub (Complex.analyticAt_cos.comp dq))))
    (by simp [edgeW,Complex.ofReal_cos])

theorem edgeComplexDenominator_analyticAt_real {N : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im) (q : Fin N→ℝ) :
    AnalyticAt ℂ (@edgeComplexDenominator N b B) (0,fun k => (q k:ℂ)) := by
  exact analyticAt_const.sub (Finset.univ.analyticAt_fun_prod
    (fun i _ => edgeComplexRoot_joint_analyticAt_real hb hB hBi q i))

theorem edgeComplexAmplitude_analyticAt_real {N : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (q : Fin N→ℝ) :
    AnalyticAt ℂ (@edgeComplexAmplitude N b B S) (0,fun k => (q k:ℂ)) := by
  have dr (i : Fin N) := edgeComplexRoot_joint_analyticAt_real hb hB hBi q i
  have dB : AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => B p.1) (0,fun k => (q k:ℂ)) :=
    hB.comp (x := ((0,fun k => (q k:ℂ)):ℂ×(Fin N→ℂ))) analyticAt_fst
  have dS : AnalyticAt ℂ (fun p : ℂ×(Fin N→ℂ) => S p.1) (0,fun k => (q k:ℂ)) :=
    hS.comp (x := ((0,fun k => (q k:ℂ)):ℂ×(Fin N→ℂ))) analyticAt_fst
  have hd (i k : Fin N) :
      1-edgeComplexRoot b B 0 (q i:ℂ)*edgeComplexRoot b B 0 (q k:ℂ)≠0 := by
    simpa using edgeRoot_pair_denominator_ne_zero hb hBi (q i) (q k)
  unfold edgeComplexAmplitude
  refine ((((dB.pow _).mul ((dS.inv hS0).pow _)).mul ?_).mul ?_).mul
    (analyticAt_const.add (Finset.univ.analyticAt_fun_prod (fun i _ => dr i)))
  · apply Finset.univ.analyticAt_fun_prod
    intro i _
    exact (analyticAt_const.mul (dr i)).div (analyticAt_const.sub ((dr i).pow 2))
      (by simpa only [pow_two] using hd i i)
  · apply (firstStrictPairs N).analyticAt_fun_prod
    intro p _
    exact ((dr p.1).mul (dr p.2)).div ((analyticAt_const.sub ((dr p.1).mul (dr p.2))).pow 2)
      (pow_ne_zero 2 (hd p.1 p.2))

/-- Jointly analytic amplitude and denominator give actual, not formal, parameter jets. -/
theorem edgeAngularDensity_jet_eventually_continuousAt_of_analytic
    {N : ℕ} {b : ℝ} {B S : ℂ→ℂ} {u : ℂ} {q : Fin N→ℝ}
    (hA : AnalyticAt ℂ (@edgeComplexAmplitude N b B S) (u,fun k => (q k:ℂ)))
    (hD : AnalyticAt ℂ (@edgeComplexDenominator N b B) (u,fun k => (q k:ℂ)))
    (hDne : edgeComplexDenominator b B (u,fun k => (q k:ℂ))≠0) (j : ℕ) :
    ∀ᶠ z : ℂ×(Fin N→ℝ) in 𝓝 (u,q),
      ContinuousAt (fun p : ℂ×(Fin N→ℝ) =>
        iteratedDeriv j (fun u => edgeAngularDensity b B S u p.2) p.1) z := by
  let G : ℂ×(Fin N→ℝ)→ℂ×(Fin N→ℂ) := fun p => (p.1,fun i => (p.2 i:ℂ))
  have hG : Continuous G := by unfold G; fun_prop
  have hJ : AnalyticAt ℂ (edgeAnalyticJet b B S j) (G (u,q)) :=
    quotientJetNumerator_joint_analyticAt hA hD j
  let F : ℂ×(Fin N→ℝ)→ℂ := fun p =>
    (firstVandermonde p.2:ℂ)^2*edgeSincFactor p.2*edgeAnalyticJet b B S j (G p)/
      edgeComplexDenominator b B (G p)^(j+1)
  have hneEv : ∀ᶠ p in 𝓝 (u,q),edgeComplexDenominator b B (G p)≠0 :=
    (hD.continuousAt.comp (f := G) (x := (u,q)) hG.continuousAt).eventually_ne hDne
  have hF : ∀ᶠ p in 𝓝 (u,q), ContinuousAt F p := by
    filter_upwards [(hG.tendsto (u,q)).eventually hJ.eventually_analyticAt,
      (hG.tendsto (u,q)).eventually hD.eventually_analyticAt,hneEv] with p hj hd hn
    apply ContinuousAt.div
    · apply ContinuousAt.mul
      · exact ((by unfold firstVandermonde; fun_prop :
          Continuous (fun p : ℂ×(Fin N→ℝ) => (firstVandermonde p.2:ℂ)^2)).continuousAt).mul
          ((edgeSincFactor_continuous N).continuousAt.comp continuousAt_snd)
      · exact hj.continuousAt.comp (f := G) (x := p) hG.continuousAt
    · exact (hd.continuousAt.comp (f := G) (x := p) hG.continuousAt).pow _
    · exact pow_ne_zero _ hn
  have heq : (fun p : ℂ×(Fin N→ℝ) =>
      iteratedDeriv j (fun u => edgeAngularDensity b B S u p.2) p.1)=ᶠ[𝓝 (u,q)] F := by
    filter_upwards [(hG.tendsto (u,q)).eventually hA.eventually_analyticAt,
      (hG.tendsto (u,q)).eventually hD.eventually_analyticAt,hneEv] with p ha hd hne
    have hu : AnalyticAt ℂ (fun u : ℂ => (u,fun i : Fin N => (p.2 i:ℂ))) p.1 :=
      analyticAt_id.prod analyticAt_const
    exact edgeAngularDensity_iteratedDeriv b B S p.2 p.1 j
      (ha.comp (f := fun u : ℂ => (u,fun i : Fin N => (p.2 i:ℂ))) (x := p.1) hu)
      (hd.comp (f := fun u : ℂ => (u,fun i : Fin N => (p.2 i:ℂ))) (x := p.1) hu) hne
  filter_upwards [hF,heq.eventuallyEq_nhds] with p hp he
  exact hp.congr_of_eventuallyEq he

theorem edgeAngularDensity_jet_eventually_continuousAt {N : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (q : Fin N→ℝ)
    (hne : edgeRootProduct b B 0 q≠1) (j : ℕ) :
    ∀ᶠ z : ℂ×(Fin N→ℝ) in 𝓝 (0,q),
      ContinuousAt (fun p : ℂ×(Fin N→ℝ) =>
        iteratedDeriv j (fun u => edgeAngularDensity b B S u p.2) p.1) z := by
  apply edgeAngularDensity_jet_eventually_continuousAt_of_analytic
    (edgeComplexAmplitude_analyticAt_real hb hB hBi hS hS0 q)
    (edgeComplexDenominator_analyticAt_real hb hB hBi q) _ j
  simpa [edgeComplexDenominator,edgeRootProduct,sub_ne_zero] using hne.symm

theorem edgeAngularDensity_jet_near_collision {N : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (j : ℕ) :
    ∀ᶠ z : ℂ×(Fin N→ℝ) in 𝓝 (0,0),
      edgeComplexDenominator b B (z.1,fun k => (z.2 k:ℂ))≠0 →
      ContinuousAt (fun p : ℂ×(Fin N→ℝ) =>
        iteratedDeriv j (fun u => edgeAngularDensity b B S u p.2) p.1) z := by
  let G : ℂ×(Fin N→ℝ)→ℂ×(Fin N→ℂ) := fun p => (p.1,fun i => (p.2 i:ℂ))
  have hG : Continuous G := by unfold G; fun_prop
  have hA := edgeComplexAmplitude_analyticAt (N := N) hb hB hBi hS hS0
  have hD := edgeComplexDenominator_analyticAt (N := N) hb hB
  have ht : Tendsto G (𝓝 (0,0)) (𝓝 (0,0)) := by simpa [G] using! hG.tendsto (0,0)
  filter_upwards [ht.eventually hA.eventually_analyticAt,
    ht.eventually hD.eventually_analyticAt] with p ha hd hn
  exact mem_of_mem_nhds (edgeAngularDensity_jet_eventually_continuousAt_of_analytic ha hd hn j)

theorem edgeAngularDensity_jet_continuousAt {N : ℕ} {b : ℝ} {B S : ℂ→ℂ}
    (hb : |b|<1) (hB : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im)
    (hS : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (q : Fin N→ℝ)
    (hne : edgeRootProduct b B 0 q≠1) (j : ℕ) :
    ContinuousAt (fun p : ℂ×(Fin N→ℝ) =>
      iteratedDeriv j (fun u => edgeAngularDensity b B S u p.2) p.1) (0,q) :=
  mem_of_mem_nhds (edgeAngularDensity_jet_eventually_continuousAt hb hB hBi hS hS0 q hne j)

end
end IsingBulk.Anisotropic.RegularEdges
