import IsingBulk.HT.Lie.SignedJets
import IsingBulk.HT.Lie.SignedBranchKernel
import IsingBulk.Tail.SourceJetIntegralEndpoint
import IsingBulk.Tail.AllBranchExteriorTruncatedDomain

/-!
Signed high-order integration on genuine compact original-branch charts.
The real smooth cutoff generates compact flux support at every stage.
The parameter neighborhood, differentiability under the integral, and
zero divergence integral are derived; no VanishingFlux certificate is
accepted as an input. The last theorem constructs actual truncated HT
charts with constants chosen before particle number and sign.
-/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.Jets IsingBulk.Lie IsingBulk.Branch IsingBulk.Tail IsingBulk.First
open MeasureTheory Set Filter Function
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem signedRegularKernel_analytic {N : ℕ} (σ : ℂ) (z : ℂ × (Fin N → ℂ))
    (hs : z.1 ≠ 0)
    (hslit : ∀ i, 1-(z.1+z.1⁻¹-Complex.cos (z.2 i))^2 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => signedRegularKernel σ t.1 t.2) z := by
  have hY : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => regularYProduct t.1 t.2) z := by
    apply Finset.analyticAt_fun_prod
    intro i _
    exact AnalyticAt.comp (g := fun t : ℂ × ℂ => regularY t.1 t.2)
      (f := fun t : ℂ × (Fin N → ℂ) => (t.1,t.2 i))
      (regularY_analytic z.1 (z.2 i) hs (hslit i))
      (analyticAt_fst.prod (analytic_coordinate i z))
  have hZ : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => regularZProduct t.1 t.2) z := by
    unfold regularZProduct
    exact (analyticAt_const.mul
      (Finset.analyticAt_fun_sum _ fun i _ => analytic_coordinate i z)).cexp
  exact (analyticAt_const.sub (analyticAt_const.mul hY)).mul
    (analyticAt_const.sub (analyticAt_const.mul hZ))

def signedComplexDensity {N : ℕ} (σ : ℂ) (v theta : ℝ)
    (Q : ℂ × (Fin N → ℂ) → ℂ) : (ℂ × (Fin N → ℂ)) → ℂ :=
  microComplexPullback v theta (fun z => Q z/signedRegularKernel σ z.1 z.2)

theorem signed_complex_models_analytic {n : ℕ} (σ : ℂ) (v theta : ℝ)
    (p q : Fin (n+1)) (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ)
    (x : AngularSpace n) (hp : ActualJetPoint v theta p q s x)
    (hQ : AnalyticAt ℂ Q (s,chartMap v theta s x))
    (hσ : signedRegularKernel σ s (chartMap v theta s x) ≠ 0) :
    AnalyticAt ℂ (signedComplexDensity σ v theta Q) (realAngularEmbedding (s,x)) ∧
      ∀ i, AnalyticAt ℂ (sourceComplexField v theta p q i) (realAngularEmbedding (s,x)) := by
  refine ⟨?_,(source_complex_models_analytic v theta p q Q s x hp hQ).2⟩
  exact microComplexPullback_analytic v theta _ _ hp.s_ne hp.re_pos hp.im_pos hp.sin_ne
    (hQ.div (signedRegularKernel_analytic σ _ hp.s_ne hp.slit) hσ)

theorem signed_compact_integral_iteratedDeriv {n : ℕ} (σ : ℂ) (v theta : ℝ) (p q : Fin (n+1))
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w)
    {K : Set (AngularSpace n)} (hK : IsCompact K) (hsupp : tsupport w ⊆ K)
    {s : ℂ} (hpoint : ∀ x∈K, ActualJetPoint v theta p q s x)
    (hQ : ∀ x∈K, AnalyticAt ℂ Q (s,chartMap v theta s x))
    (hσ : ∀ x∈K, signedRegularKernel σ s (chartMap v theta s x) ≠ 0) (j : ℕ) :
    iteratedDeriv j (fun t => ∫ x, signedInitialSourceDensity σ v theta w Q t x) s =
      ∫ x, ((lieStep (actualField v theta p q))^[j] (signedInitialSourceDensity σ v theta w Q)) s x := by
  let A := signedInitialSourceDensity σ v theta w Q
  let V := actualField v theta p q
  let F := signedComplexDensity σ v theta Q
  let B := sourceComplexField v theta p q
  let Omega : Set (ℂ × AngularSpace n) := {z | AnalyticAt ℂ F (realAngularEmbedding z) ∧
      ∀ i, AnalyticAt ℂ (B i) (realAngularEmbedding z)}
  have hO : IsOpen Omega := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hc : ContinuousAt (@realAngularEmbedding (n+1)) z := (realAngularEmbedding_contDiff (n+1)).continuous.continuousAt
    have hF' := hc.eventually hz.1.eventually_analyticAt
    have hB' := Filter.eventually_all.mpr (fun i => hc.eventually (hz.2 i).eventually_analyticAt)
    exact hF'.and hB'
  have hcenter : ∀ x∈K,(s,x)∈Omega := fun x hx => signed_complex_models_analytic σ v theta p q Q s x (hpoint x hx) (hQ x hx) (hσ x hx)
  have hevent : ∀ᶠ t in 𝓝 s, ∀ x∈K,(t,x)∈Omega :=
    hK.eventually_forall_of_forall_eventually (fun x hx => hO.mem_nhds (hcenter x hx))
  obtain ⟨U,hUsub,hU,hs⟩ := mem_nhds_iff.mp hevent
  have hA : ParameterSmoothOn Omega A := by
    intro z hz
    constructor
    · exact weighted_analytic_real_joint w hw F z hz.1
    · have ha := hz.1.comp (f := fun t : ℂ => (t,fun i => (z.2 i:ℂ)))
        (analyticAt_id.prod analyticAt_const)
      exact (differentiableAt_const (w z.2:ℂ)).mul ha.differentiableAt
  have hV : ∀ i, ParameterSmoothOn Omega (fun t x => V t x i) := by
    intro i z hz
    have ha := hz.2 i
    constructor
    · exact (ha.contDiffAt.restrict_scalars ℝ).comp z (realAngularEmbedding_contDiff (n+1)).contDiffAt
    · exact (ha.comp (f := fun t : ℂ => (t,fun k => (z.2 k:ℂ)))
        (analyticAt_id.prod analyticAt_const)).differentiableAt
  have hstage (k : ℕ) := hA.iterate_lieStep hO V A hV k
  have hsA : ∀ t∈U,support (A t) ⊆ K := by
    intro t ht x hx
    have hwx : w x≠0 := by intro he; simp [A,signedInitialSourceDensity,he] at hx
    exact hsupp (subset_closure hwx)
  have hsiter (k : ℕ) (t : ℂ) (ht : t∈U) : tsupport (((lieStep V)^[k] A) t) ⊆ K :=
    iterate_lieStep_support_subset V A hU hK.isClosed hsA k t ht
  have hflux (k : ℕ) (t : ℂ) (ht : t∈U) (i : Fin (n+1)) :
      ContDiff ℝ 1 (fun x => V t x i*((lieStep V)^[k] A) t x) := by
    have hsupport : tsupport (fun x => V t x i*((lieStep V)^[k] A) t x) ⊆ K :=
      tsupport_mul_subset_right.trans (hsiter k t ht)
    apply (contDiff_of_closed_support _ hsupport _).of_le (by simp)
    intro x hx
    have hz := hUsub ht x hx
    exact ((hV i (t,x) hz).1.comp x (contDiffAt_const.prodMk contDiffAt_id)).mul
      ((hstage k (t,x) hz).1.comp x (contDiffAt_const.prodMk contDiffAt_id))
  have hid := compact_support_iterate_lieStep_integral_on hK hU V A j
    (fun k hk t ht => subset_closure.trans (hsiter k t ht))
    (fun k hk z hz => (hstage k z (hUsub hz.1 z.2 hz.2)).1.continuousAt.continuousWithinAt)
    (fun k hk z hz => ((hstage k).paramDeriv hO z (hUsub hz.1 z.2 hz.2)).1.continuousAt.continuousWithinAt)
    (fun k hk t ht x hx => (hstage k (t,x) (hUsub ht x hx)).2)
    (fun k hk t ht i => hflux k t ht i)
  simpa only [iteratedDeriv_eq_iterate,A,V] using (hid hs).symm


/-- The signed gap and actual center chart construct the open neighborhoods
needed by the all-order recurrence. -/
theorem signed_source_point_all_order {n : ℕ} (σ : ℂ) (v theta : ℝ)
    (p q : Fin (n+1)) (hpq : p ≠ q) (s : ℂ) (x : AngularSpace n)
    (hv : v < 0) (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (hpoint : ActualJetPoint v theta p q s x)
    (hQ : AnalyticAt ℂ Q (s,chartMap v theta s x))
    (hσ : signedRegularKernel σ s (chartMap v theta s x) ≠ 0) (j : ℕ) :
    ((lieStep (actualField v theta p q))^[j] (signedInitialSourceDensity σ v theta w Q)) s x =
      signedSourceTermSum σ p q v theta w Q j s x := by
  have hc := (microcore_joint_chart_continuous v theta s x
    ⟨hpoint.s_ne,hpoint.re_pos,hpoint.im_pos,hpoint.g_pos,hpoint.sin_ne,hpoint.slit⟩).1
  have hkernel : ContinuousAt
      (fun z : ℂ × AngularSpace n => signedRegularKernel σ z.1
        (chartMap v theta z.1 z.2)) (s,x) := by
    have hK : ContinuousAt
        (fun z : ℂ × (Fin (n+1) → ℂ) => signedRegularKernel σ z.1 z.2)
        (s,chartMap v theta s x) :=
      (signedRegularKernel_analytic σ (s,chartMap v theta s x)
        hpoint.s_ne hpoint.slit).continuousAt
    exact hK.comp' (x := (s,x))
      (f := fun z : ℂ × AngularSpace n => (z.1,chartMap v theta z.1 z.2))
      (g := fun z : ℂ × (Fin (n+1) → ℂ) => signedRegularKernel σ z.1 z.2) hc
  have hgap : ∀ᶠ z : ℂ × AngularSpace n in 𝓝 (s,x),
      signedRegularKernel σ z.1 (chartMap v theta z.1 z.2) ≠ 0 :=
    hkernel.eventually_ne hσ
  have he := (actualJetPoint_eventually_original v theta p q s x hv hpoint).and
    ((hc.eventually hQ.eventually_analyticAt).and hgap)
  obtain ⟨U,R,hU,hs,hR,hx,hsub⟩ := mem_nhds_prod_iff'.mp he
  exact signed_sourceJetTerms_all_order_analytic σ p q hpq v theta w Q U R hU hR hw
    (fun t ht y hy => (hsub (show (t,y)∈U×ˢR from ⟨ht,hy⟩)).1)
    (fun t ht y hy => (hsub (show (t,y)∈U×ˢR from ⟨ht,hy⟩)).2.2)
    (fun t ht y hy => (hsub (show (t,y)∈U×ˢR from ⟨ht,hy⟩)).2.1) j s hs x hx

theorem signedSourceTermSum_support_subset {n : ℕ} (σ : ℂ) (v theta : ℝ)
    (p q : Fin (n+1)) (w : AngularSpace n → ℝ)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (j : ℕ) (s : ℂ) :
    support (signedSourceTermSum σ p q v theta w Q j s) ⊆ tsupport w := by
  intro x hx
  by_contra hn
  apply hx
  unfold signedSourceTermSum
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨T,hT,rfl⟩ := List.mem_map.mp ha
  have hcut : cutoffJet T.cutoff w x=0 := by
    by_contra h
    exact hn (cutoffJet_tsupport_subset T.cutoff w (subset_closure h))
  simp [signedSourceValue,hcut]

/-- Actual differentiated signed integral equals the literal finite source
sum. Compact flux cancellation is proved at every preceding stage. -/
theorem signed_compact_integral_sourceTermSum {n : ℕ} (σ : ℂ)
    (v theta : ℝ) (hv : v < 0) (p q : Fin (n+1)) (hpq : p ≠ q)
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (w : AngularSpace n → ℝ)
    (hw : ContDiff ℝ ∞ w) {K : Set (AngularSpace n)} (hK : IsCompact K)
    (hsupp : tsupport w ⊆ K) {s : ℂ}
    (hpoint : ∀ x∈K, ActualJetPoint v theta p q s x)
    (hQ : ∀ x∈K, AnalyticAt ℂ Q (s,chartMap v theta s x))
    (hσ : ∀ x∈K, signedRegularKernel σ s (chartMap v theta s x) ≠ 0) (j : ℕ) :
    iteratedDeriv j (fun t => ∫ x, signedInitialSourceDensity σ v theta w Q t x) s =
      ∫ x, signedSourceTermSum σ p q v theta w Q j s x := by
  rw [signed_compact_integral_iteratedDeriv σ v theta p q Q w hw hK hsupp hpoint hQ hσ j]
  let A := signedInitialSourceDensity σ v theta w Q
  let V := actualField v theta p q
  have hsA : ∀ t∈(univ : Set ℂ),support (A t) ⊆ K := by
    intro t ht x hx
    have hwx : w x≠0 := by intro he; simp [A,signedInitialSourceDensity,he] at hx
    exact hsupp (subset_closure hwx)
  have hsiter := iterate_lieStep_support_subset V A isOpen_univ hK.isClosed hsA j s (mem_univ s)
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x∈K
  · exact signed_source_point_all_order σ v theta p q hpq s x hv w hw Q
      (hpoint x hx) (hQ x hx) (hσ x hx) j
  · have hzero : ((lieStep V)^[j] A) s x=0 := by
      by_contra h
      exact hx (hsiter (subset_closure h))
    have hterms : signedSourceTermSum σ p q v theta w Q j s x=0 := by
      by_contra h
      exact hx (hsupp (signedSourceTermSum_support_subset σ v theta p q w Q j s h))
    exact hzero.trans hterms.symm

/-- All physical original-branch chart data, compact smooth excision weights,
and signed gaps are constructed. This is the exact truncated integral
identity, before removal of the two excision scales. -/
theorem signed_truncated_source_integral (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ α : ℝ,
      ∀ n M : ℕ, ∀ p q : Fin (n+1), p ≠ q → ∀ h : ℝ, 0 < h →
      ∀ w : AngularSpace n → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ microcoreCube (n+1) r → ∀ j : ℕ,
      let W := allBranchTruncatedWeight M h p q w
      let Q := unfactoredNumerator
        (fun z : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude z.1 z.2)
      iteratedDeriv j (fun t => ((n+1).factorial:ℂ)⁻¹ *
        ∫ u, signedInitialSourceDensity (Complex.exp (Complex.I*(α:ℂ)))
          (-d.c₀*ε) d.thetaB W Q t u) (radialParameter d.theta ε) =
        ((n+1).factorial:ℂ)⁻¹ * ∫ u,
          signedSourceTermSum (Complex.exp (Complex.I*(α:ℂ))) p q
            (-d.c₀*ε) d.thetaB W Q j (radialParameter d.theta ε) u := by
  obtain ⟨rA,hrA,hdata⟩ := allBranchExterior_truncated_source_data d
  obtain ⟨a,rK,ha,hrK,hgap⟩ := signed_original_kernel_gap_and_floor d hcsmall
  let r := min rA rK
  have hr : 0 < r := lt_min hrA hrK
  refine ⟨r,hr,?_⟩
  intro ε hε hεr α n M p q hpq h hh w hw hsupp j
  have hsuppA : tsupport w ⊆ microcoreCube (n+1) rA := by
    intro u hu
    exact (mem_microcoreCube rA u).mpr (fun i =>
      ((mem_microcoreCube r u).mp (hsupp hu) i).trans (min_le_left _ _))
  obtain ⟨hsmooth,hcompact,hpoint⟩ := hdata ε hε
    (hεr.trans (min_le_left _ _)) n M p q h hh w hw hsuppA
  dsimp only
  rw [iteratedDeriv_const_mul_field]
  congr 1
  apply signed_compact_integral_sourceTermSum _ _ _ (by nlinarith [d.c₀_pos])
    p q hpq _ _ hsmooth hcompact (Subset.refl _)
    (fun u hu => (hpoint u hu).1) (fun u hu => (hpoint u hu).2)
  intro u hu
  have hub := (mem_microcoreCube r u).mp
    (hsupp (allBranchTruncatedWeight_support M hh p q w hu).1)
  exact (hgap ε hε (hεr.trans (min_le_right _ _)) α n u
    (fun i => (hub i).trans (min_le_right _ _))).1


end
end IsingBulk.HT.Lie
