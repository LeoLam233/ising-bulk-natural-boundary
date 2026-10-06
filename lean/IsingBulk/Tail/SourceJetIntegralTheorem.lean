import IsingBulk.Tail.ParameterSmoothLie
import IsingBulk.Tail.MicrocoreIntegralTheorem
import IsingBulk.Analysis.JetsAllOrder

/-! Actual original-chart selected-field compact Lie integration. Joint
regularity and every stage derivative are derived from genuine analytic
complex models and real smooth cutoffs, not supplied as flux certificates. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie IsingBulk.Branch MeasureTheory Set Filter Function
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1200000

def sourceComplexField {N : ℕ} (v theta : ℝ) (p q i : Fin N)
    (z : ℂ × (Fin N → ℂ)) : ℂ :=
  selectedField (fun k => chartA z.1 v theta (z.2 k)) (fun k => chartB z.1 v theta (z.2 k)) p q i

def sourceComplexDensity {N : ℕ} (v theta : ℝ) (Q : ℂ × (Fin N → ℂ) → ℂ) :
    (ℂ × (Fin N → ℂ)) → ℂ :=
  microComplexPullback v theta (fun z => Q z/regularKernel z.1 z.2)

theorem source_complex_models_analytic {n : ℕ} (v theta : ℝ) (p q : Fin (n+1))
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ) (x : AngularSpace n)
    (hp : ActualJetPoint v theta p q s x) (hQ : AnalyticAt ℂ Q (s,chartMap v theta s x)) :
    AnalyticAt ℂ (sourceComplexDensity v theta Q) (realAngularEmbedding (s,x)) ∧
      ∀ i, AnalyticAt ℂ (sourceComplexField v theta p q i) (realAngularEmbedding (s,x)) := by
  let z := realAngularEmbedding (s,x)
  have hY (i : Fin (n+1)) : AnalyticAt ℂ (fun t : ℂ × (Fin (n+1) → ℂ) => angularY v theta (t.2 i)) z := by
    unfold angularY
    exact (analyticAt_const.add (((analytic_coordinate i z).sub analyticAt_const).mul analyticAt_const)).cexp
  have hG (i : Fin (n+1)) : AnalyticAt ℂ (fun t : ℂ × (Fin (n+1) → ℂ) => angularG v theta (t.2 i)) z := by
    exact (analyticAt_const.mul ((hY i).sub ((hY i).inv (Complex.exp_ne_zero _)))).div_const
  have hW (i : Fin (n+1)) : AnalyticAt ℂ (fun t : ℂ × (Fin (n+1) → ℂ) => chartW t.1 v theta (t.2 i)) z := by
    exact (analyticAt_fst.add (analyticAt_fst.inv hp.s_ne)).sub
      (((hY i).add ((hY i).inv (Complex.exp_ne_zero _))).div_const)
  have hphase (i : Fin (n+1)) : AnalyticAt ℂ (fun t : ℂ × (Fin (n+1) → ℂ) => chartPhase t.1 v theta (t.2 i)) z :=
    (lowerArccos_analytic_upper_quadrant _ (hp.re_pos i) (hp.im_pos i)).comp
      (f := fun t : ℂ × (Fin (n+1) → ℂ) => chartW t.1 v theta (t.2 i)) (hW i)
  have hB (i : Fin (n+1)) : AnalyticAt ℂ (fun t : ℂ × (Fin (n+1) → ℂ) => chartB t.1 v theta (t.2 i)) z :=
    (hG i).div (Complex.analyticAt_sin.comp (hphase i)) (hp.sin_ne i)
  have hA (i : Fin (n+1)) : AnalyticAt ℂ (fun t : ℂ × (Fin (n+1) → ℂ) => chartA t.1 v theta (t.2 i)) z := by
    have hn : angularG v theta (x i:ℂ) ≠ 0 := by intro hz; simpa [hz] using hp.g_pos i
    exact (analyticAt_const.sub ((analyticAt_fst.pow 2).inv (pow_ne_zero 2 hp.s_ne))).div
      (hG i).neg (neg_ne_zero.mpr hn)
  constructor
  · exact microComplexPullback_analytic v theta _ _ hp.s_ne hp.re_pos hp.im_pos hp.sin_ne
      (hQ.div (regularKernel_analytic _ hp.s_ne hp.slit) hp.kernel_ne)
  · intro i
    have hsum := Finset.analyticAt_fun_sum Finset.univ (fun k _ => hA k)
    have hleft : AnalyticAt ℂ (fun t : ℂ × (Fin (n+1) → ℂ) =>
        if i=p then (∑ k,chartA t.1 v theta (t.2 k))*chartB t.1 v theta (t.2 q)/
          (chartB t.1 v theta (t.2 p)-chartB t.1 v theta (t.2 q)) else 0) z := by
      by_cases hi : i=p
      · simp only [hi,ite_true]
        exact (hsum.mul (hB q)).div ((hB p).sub (hB q)) hp.b_ne
      · simp only [hi,ite_false]; exact analyticAt_const
    have hright : AnalyticAt ℂ (fun t : ℂ × (Fin (n+1) → ℂ) =>
        if i=q then (∑ k,chartA t.1 v theta (t.2 k))*chartB t.1 v theta (t.2 p)/
          (chartB t.1 v theta (t.2 p)-chartB t.1 v theta (t.2 q)) else 0) z := by
      by_cases hi : i=q
      · simp only [hi,ite_true]
        exact (hsum.mul (hB p)).div ((hB p).sub (hB q)) hp.b_ne
      · simp only [hi,ite_false]; exact analyticAt_const
    exact ((hA i).add hleft).sub hright

theorem source_compact_integral_iteratedDeriv {n : ℕ} (v theta : ℝ) (p q : Fin (n+1))
    (Q : ℂ × (Fin (n+1) → ℂ) → ℂ) (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w)
    {K : Set (AngularSpace n)} (hK : IsCompact K) (hsupp : tsupport w ⊆ K)
    {s : ℂ} (hpoint : ∀ x∈K, ActualJetPoint v theta p q s x)
    (hQ : ∀ x∈K, AnalyticAt ℂ Q (s,chartMap v theta s x)) (j : ℕ) :
    iteratedDeriv j (fun t => ∫ x, initialSourceDensity v theta w Q t x) s =
      ∫ x, ((lieStep (actualField v theta p q))^[j] (initialSourceDensity v theta w Q)) s x := by
  let A := initialSourceDensity v theta w Q
  let V := actualField v theta p q
  let F := sourceComplexDensity v theta Q
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
  have hcenter : ∀ x∈K,(s,x)∈Omega := fun x hx => source_complex_models_analytic v theta p q Q s x (hpoint x hx) (hQ x hx)
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
    have hwx : w x≠0 := by intro he; simp [A,initialSourceDensity,he] at hx
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

end
end IsingBulk.Tail
