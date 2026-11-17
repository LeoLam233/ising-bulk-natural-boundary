import IsingBulk.AnisoF002.C03.RegularParameterJets
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Actual repeated differentiation under compact parameter integrals

Only generic joint analyticity and a finite measure carried by a compact
set are used.  A common parameter disk and derivative majorants are
constructed by compactness, rather than supplied as extra hypotheses.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [MeasurableSpace X] [BorelSpace X] in
theorem joint_analytic_compact_parameter_disk {f : ℂ × E → ℂ} {g : X → E}
    {K : Set X} {t : ℂ} (hK : IsCompact K) (hg : Continuous g)
    (hf : ∀ x ∈ K, AnalyticAt ℂ f (t, g x)) :
    ∃ r : ℝ, 0 < r ∧ ∀ u ∈ Metric.closedBall t r, ∀ x ∈ K,
      AnalyticAt ℂ f (u, g x) := by
  have hm : Continuous (fun p : ℂ × X => (p.1, g p.2)) :=
    continuous_fst.prodMk (hg.comp continuous_snd)
  have ho : IsOpen {p : ℂ × X | AnalyticAt ℂ f (p.1, g p.2)} :=
    (isOpen_analyticAt ℂ f).preimage hm
  have hs : ({t} : Set ℂ) ×ˢ K ⊆ {p : ℂ × X | AnalyticAt ℂ f (p.1, g p.2)} := by
    rintro p ⟨hp, hx⟩
    change AnalyticAt ℂ f (p.1, g p.2)
    rw [Set.mem_singleton_iff.mp hp]
    exact hf p.2 hx
  obtain ⟨r, hr, hsub⟩ := (isCompact_singleton.prod hK).exists_cthickening_subset_open ho hs
  refine ⟨r, hr, ?_⟩
  intro u hu x hx
  apply hsub (a := (u, x))
  apply Metric.mem_cthickening_of_dist_le (u, x) (t, x) r (({t} : Set ℂ) ×ˢ K)
    ⟨by simp, hx⟩
  simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg : 0 ≤ dist u t)] using
    Metric.mem_closedBall.mp hu

theorem integrable_of_carried_compact {μ : Measure X} [IsFiniteMeasure μ]
    {K : Set X} {F : X → ℂ} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K)
    (hF : ContinuousOn F K) : Integrable F μ := by
  have h := hF.integrableOn_compact (μ := μ) hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h

theorem integral_hasDerivAt_of_joint_analytic {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℂ × E → ℂ} {g : X → E} {K : Set X} {t : ℂ}
    (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K) (hg : Continuous g)
    (hf : ∀ x ∈ K, AnalyticAt ℂ f (t, g x)) :
    Integrable (fun x => deriv (fun u : ℂ => f (u, g x)) t) μ ∧
      HasDerivAt (fun u : ℂ => ∫ x, f (u, g x) ∂μ)
        (∫ x, deriv (fun u : ℂ => f (u, g x)) t ∂μ) t := by
  obtain ⟨r, hr, hnear⟩ := joint_analytic_compact_parameter_disk hK hg hf
  let F : ℂ → X → ℂ := fun u x => f (u, g x)
  let F' : ℂ → X → ℂ := fun u x => deriv (fun v : ℂ => f (v, g x)) u
  have hm : Continuous (fun p : ℂ × X => (p.1, g p.2)) :=
    continuous_fst.prodMk (hg.comp continuous_snd)
  have h0 (u : ℂ) (hu : u ∈ Metric.closedBall t r) : ContinuousOn (F u) K := by
    intro x hx
    exact ((hnear u hu x hx).continuousAt.comp
      (f := fun y : X => (u, g y)) (continuousAt_const.prodMk hg.continuousAt)).continuousWithinAt
  have h1 : ContinuousOn (fun p : ℂ × X => F' p.1 p.2) (Metric.closedBall t r ×ˢ K) := by
    intro p hp
    have ha := parameterIteratedDeriv_analyticAt (hnear p.1 hp.1 p.2 hp.2) 1
    have hc := ha.continuousAt.comp (f := fun q : ℂ × X => (q.1, g q.2)) hm.continuousAt
    simpa only [iteratedDeriv_one, Function.comp_def] using hc.continuousWithinAt
  have ht : t ∈ Metric.closedBall t r := Metric.mem_closedBall_self hr.le
  have h1t : ContinuousOn (F' t) K := by
    intro x hx
    have ha := parameterIteratedDeriv_analyticAt (hf x hx) 1
    have hc := ha.continuousAt.comp
      (f := fun y : X => (t, g y)) (continuousAt_const.prodMk hg.continuousAt)
    simpa only [iteratedDeriv_one, Function.comp_def] using hc.continuousWithinAt
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t r).prod hK).exists_bound_of_continuousOn h1
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := Metric.closedBall t r) (bound := fun _ => M)
    (Metric.closedBall_mem_nhds t hr)
  · filter_upwards [Metric.closedBall_mem_nhds t hr] with u hu
    exact (integrable_of_carried_compact hK hμ (h0 u hu)).aestronglyMeasurable
  · exact integrable_of_carried_compact hK hμ (h0 t ht)
  · exact (integrable_of_carried_compact hK hμ h1t).aestronglyMeasurable
  · exact hμ.mono fun x hx u hu => hM (u, x) ⟨hu, hx⟩
  · exact integrable_const M
  · exact hμ.mono fun x hx u hu =>
      ((hnear u hu x hx).comp (f := fun v : ℂ => (v, g x))
        (analyticAt_id.prod analyticAt_const)).differentiableAt.hasDerivAt

/-- Every ordinary iterated derivative equals the integral of the actual
iterated derivative of the parameter slice. -/
theorem iteratedDeriv_integral_of_joint_analytic {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℂ × E → ℂ} {g : X → E} {K : Set X} {t : ℂ}
    (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K) (hg : Continuous g)
    (hf : ∀ x ∈ K, AnalyticAt ℂ f (t, g x)) (j : ℕ) :
    iteratedDeriv j (fun u : ℂ => ∫ x, f (u, g x) ∂μ) t =
      ∫ x, iteratedDeriv j (fun u : ℂ => f (u, g x)) t ∂μ := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    obtain ⟨r, hr, hnear⟩ := joint_analytic_compact_parameter_disk hK hg hf
    have heq : (fun u : ℂ => iteratedDeriv j (fun v : ℂ => ∫ x, f (v, g x) ∂μ) u) =ᶠ[𝓝 t]
        fun u : ℂ => ∫ x, iteratedDeriv j (fun v : ℂ => f (v, g x)) u ∂μ := by
      filter_upwards [Metric.closedBall_mem_nhds t hr] with u hu
      exact ih (hnear u hu)
    have hd := (integral_hasDerivAt_of_joint_analytic (μ := μ)
      (f := fun p : ℂ × E => iteratedDeriv j (fun v : ℂ => f (v, p.2)) p.1)
      hK hμ hg (fun x hx => parameterIteratedDeriv_analyticAt (hf x hx) j)).2
    rw [iteratedDeriv_succ]
    exact heq.deriv_eq.trans (by simpa only [iteratedDeriv_succ] using hd.deriv)

end
end IsingBulk.AnisoF002.RegularTail.C03
