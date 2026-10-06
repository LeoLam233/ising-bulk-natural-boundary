import IsingBulk.Tail.MicrocoreComplexChart
import IsingBulk.Tail.MicrocoreAllOrder
import IsingBulk.Tail.MicrocoreLocalDensityJets
import IsingBulk.Tail.MicrocoreIntegralRegularity
import IsingBulk.First.JointPoleRegularity

/-! Actual finite Lie terms inherit joint real smoothness, including their
complex parameter derivatives, from the constructed complex chart. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie IsingBulk.First Filter Set
open scoped Topology ContDiff

def realAngularEmbedding {N : ℕ} (p : ℂ × (Fin N → ℝ)) : ℂ × (Fin N → ℂ) :=
  (p.1,fun i => (p.2 i:ℂ))

theorem realAngularEmbedding_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (@realAngularEmbedding N) := by
  apply contDiff_fst.prodMk
  apply contDiff_pi.mpr
  intro i
  exact Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ i).comp contDiff_snd)

theorem weighted_analytic_real_joint {N : ℕ} (w : (Fin N → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (F : ℂ × (Fin N → ℂ) → ℂ) (p : ℂ × (Fin N → ℝ))
    (hF : AnalyticAt ℂ F (realAngularEmbedding p)) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => (w z.2:ℂ)*F (realAngularEmbedding z)) p := by
  have hc : ContDiffAt ℝ ∞ F (realAngularEmbedding p) := hF.contDiffAt.restrict_scalars ℝ
  have hf := hc.comp p (realAngularEmbedding_contDiff N).contDiffAt
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p (hw.contDiffAt.comp p contDiffAt_snd)).mul hf

theorem weighted_analytic_parameter_joint {N : ℕ} (w : (Fin N → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (F : ℂ × (Fin N → ℂ) → ℂ) (p : ℂ × (Fin N → ℝ))
    (hF : AnalyticAt ℂ F (realAngularEmbedding p)) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      deriv (fun t => (w z.2:ℂ)*F (t,fun i => (z.2 i:ℂ))) z.1) p := by
  have ha := weighted_analytic_real_joint w hw (parameterDeriv F) p (parameterDeriv_analyticAt hF)
  have he : (fun z : ℂ × (Fin N → ℝ) =>
      deriv (fun t => (w z.2:ℂ)*F (t,fun i => (z.2 i:ℂ))) z.1) =ᶠ[𝓝 p]
      (fun z => (w z.2:ℂ)*parameterDeriv F (realAngularEmbedding z)) := by
    filter_upwards [(realAngularEmbedding_contDiff N).continuous.continuousAt.eventually
      hF.eventually_analyticAt] with z hz
    have hd : DifferentiableAt ℂ (fun t => F (t,fun i => (z.2 i:ℂ))) z.1 :=
      (hz.comp (f := fun t : ℂ => (t,fun i => (z.2 i:ℂ)))
        (analyticAt_id.prod analyticAt_const)).differentiableAt
    exact (hd.hasDerivAt.const_mul (w z.2:ℂ)).deriv
  exact ha.congr_of_eventuallyEq he

theorem MicrocoreJetTerm.sourceValue_joint {n : ℕ} (T : MicrocoreJetTerm (n+1))
    (v theta : ℝ) (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w)
    (s : ℂ) (x : AngularSpace n) (hp : MicrocoreJetPoint v theta s x)
    (hT : AnalyticAt ℂ T.regularPart (s,chartMap v theta s x)) :
    ContDiffAt ℝ ∞ (fun z : ℂ × AngularSpace n => T.sourceValue v theta w z.1 z.2) (s,x) ∧
    ContDiffAt ℝ ∞ (fun z : ℂ × AngularSpace n =>
      deriv (fun t => T.sourceValue v theta w t z.2) z.1) (s,x) := by
  have ha : AnalyticAt ℂ (microComplexPullback v theta T.regularPart)
      (realAngularEmbedding (s,x)) :=
    microComplexPullback_analytic v theta T.regularPart _ hp.s_ne hp.re_pos hp.im_pos hp.sin_ne hT
  exact ⟨weighted_analytic_real_joint (cutoffJet T.cutoff w) (cutoffJet_contDiff _ _ hw) _ _ ha,
    weighted_analytic_parameter_joint (cutoffJet T.cutoff w) (cutoffJet_contDiff _ _ hw) _ _ ha⟩


theorem list_sum_contDiffAt {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : List ι) (F : ι → E → ℂ) (x : E)
    (hF : ∀ i ∈ L, ContDiffAt ℝ ∞ (F i) x) :
    ContDiffAt ℝ ∞ (fun y => (L.map (fun i => F i y)).sum) x := by
  induction L with
  | nil => exact contDiffAt_const
  | cons a L ih =>
    exact (hF a (by simp)).add (ih (fun i hi => hF i (by simp [hi])))

theorem list_parameter_deriv_sum {ι : Type*} (L : List ι) (F : ι → ℂ → ℂ) (s : ℂ)
    (hF : ∀ i ∈ L, DifferentiableAt ℂ (F i) s) :
    DifferentiableAt ℂ (fun t => (L.map (fun i => F i t)).sum) s ∧
    deriv (fun t => (L.map (fun i => F i t)).sum) s =
      (L.map (fun i => deriv (F i) s)).sum := by
  induction L with
  | nil => simp [differentiableAt_const]
  | cons a L ih =>
    obtain ⟨hL,he⟩ := ih (fun i hi => hF i (by simp [hi]))
    have ha := hF a (by simp)
    simp only [List.map_cons,List.sum_cons]
    exact ⟨ha.fun_add hL,by rw [deriv_fun_add ha hL,he]⟩

theorem microcoreTermSum_joint_regular {n : ℕ} (v theta : ℝ)
    (w : AngularSpace n → ℝ) (hw : ContDiff ℝ ∞ w)
    (F : ℂ × (Fin (n+1) → ℂ) → ℂ) (j : ℕ) (s : ℂ) (x : AngularSpace n)
    (hp : MicrocoreJetPoint v theta s x)
    (hF : AnalyticAt ℂ F (s,chartMap v theta s x)) :
    ContDiffAt ℝ ∞ (fun z : ℂ × AngularSpace n => microcoreTermSum v theta w F j z.1 z.2) (s,x) ∧
    ContDiffAt ℝ ∞ (fun z : ℂ × AngularSpace n =>
      deriv (fun t => microcoreTermSum v theta w F j t z.2) z.1) (s,x) := by
  have hterms := microcoreJetTerms_analytic F j (s,chartMap v theta s x) hF hp.regularA_analytic
  have hreg := fun T hT => MicrocoreJetTerm.sourceValue_joint T v theta w hw s x hp (hterms T hT)
  constructor
  · exact list_sum_contDiffAt _ _ (s,x) (fun T hT => (hreg T hT).1)
  · have hc : ContDiffAt ℝ ∞ (fun z : ℂ × AngularSpace n =>
        ((microcoreJetTerms F j).map (fun T => deriv (fun t => T.sourceValue v theta w t z.2) z.1)).sum)
        (s,x) := list_sum_contDiffAt _ _ (s,x) (fun T hT => (hreg T hT).2)
    apply hc.congr_of_eventuallyEq
    obtain ⟨hchart,hpoint⟩ := microcore_joint_chart_continuous v theta s x hp
    filter_upwards [hpoint,hchart.eventually hF.eventually_analyticAt] with z hz hzf
    apply (list_parameter_deriv_sum _ _ z.1 _).2
    intro T hT
    have ht := microcoreJetTerms_analytic F j _ hzf hz.regularA_analytic T hT
    exact (MicrocoreJetTerm.source_differentiable T v theta z.1 z.2 w hw hz.s_ne
      hz.re_pos hz.im_pos hz.sin_ne ht).1


end
end IsingBulk.Tail
