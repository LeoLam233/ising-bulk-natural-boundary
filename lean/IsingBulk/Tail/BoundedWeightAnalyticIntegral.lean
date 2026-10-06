import IsingBulk.First.CompactAnalyticShapeIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Fixed bounded measurable weights can be kept outside every parameter
derivative of a compact analytic integral. Uniformly bounded convergent weights
then give convergence of the actual derivatives, not merely formal jets.
The compact bounds here are qualitative and may depend on the fixed center. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter MeasureTheory Metric
open scoped Topology

theorem hasDerivAt_compact_bounded_weight_integral
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {U : Set ℂ} {s : ℂ} (hU : U ∈ 𝓝 s) (F G : ℂ → X → ℂ)
    (hF : ContinuousOn (fun z : ℂ × X => F z.1 z.2) (U ×ˢ K))
    (hG : ContinuousOn (fun z : ℂ × X => G z.1 z.2) (U ×ˢ K))
    (hd : ∀ t ∈ U, ∀ x ∈ K, HasDerivAt (fun z => F z x) (G t x) t)
    (w : X → ℂ) (hw : AEStronglyMeasurable w (μ.restrict K))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ.restrict K, ‖w x‖ ≤ B) :
    HasDerivAt (fun t => ∫ x in K, w x*F t x ∂μ) (∫ x in K, w x*G s x ∂μ) s := by
  obtain ⟨ε,hε,hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hsU := mem_of_mem_nhds hU
  have hball : closedBall s (ε/2) ⊆ U :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  have hFc (t : ℂ) (ht : t ∈ U) : ContinuousOn (F t) K :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨ht,hx⟩)
  have hGc (t : ℂ) (ht : t ∈ U) : ContinuousOn (G t) K :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨ht,hx⟩)
  have hFi (t : ℂ) (ht : t ∈ U) : Integrable (fun x => w x*F t x) (μ.restrict K) :=
    ((hFc t ht).integrableOn_compact hK).bdd_mul hw hb
  obtain ⟨C,hC⟩ := ((isCompact_closedBall s (ε/2)).prod hK).exists_bound_of_continuousOn
    (hG.mono (prod_mono hball Subset.rfl))
  have hbound : Integrable (fun _x : X => B*C) (μ.restrict K) :=
    integrableOn_const hK.measure_lt_top.ne
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (closedBall_mem_nhds s (by linarith : 0 < ε/2))
    (Filter.Eventually.mono hU (fun t ht => (hFi t ht).aestronglyMeasurable))
    (hFi s hsU) (hw.mul ((hGc s hsU).integrableOn_compact hK).aestronglyMeasurable)
    ?_ hbound ?_).2
  · filter_upwards [ae_restrict_mem hK.measurableSet,hb] with x hx hbx
    intro t ht
    rw [norm_mul]
    exact mul_le_mul hbx (hC (t,x) ⟨ht,hx⟩) (norm_nonneg _) hB
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    intro t ht
    exact (hd t (hball ht) x hx).const_mul (w x)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_bounded_weight_integral_iteratedDeriv
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ × E → ℂ) (psi : X → E) (hpsi : Continuous psi)
    (hF : ∀ s ∈ U, ∀ x ∈ K, AnalyticAt ℂ F (s,psi x))
    (w : X → ℂ) (hw : AEStronglyMeasurable w (μ.restrict K))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ.restrict K, ‖w x‖ ≤ B)
    (j : ℕ) {s : ℂ} (hs : s ∈ U) :
    iteratedDeriv j (fun t => ∫ x in K, w x*F (t,psi x) ∂μ) s =
      ∫ x in K, w x*iteratedDeriv j (fun t => F (t,psi x)) s ∂μ := by
  let H := fun k t x => jointParameterJet F k (t,psi x)
  have hc (k : ℕ) : ContinuousOn (fun z : ℂ × X => H k z.1 z.2) (U ×ˢ K) := by
    intro z hz
    have ha := (jointParameterJet_analyticAt (hF z.1 hz.1 z.2 hz.2) k).continuousAt
    exact (ha.comp (f := fun z : ℂ × X => (z.1,psi z.2))
      (continuous_fst.prodMk (hpsi.comp continuous_snd)).continuousAt).continuousWithinAt
  have hd (k : ℕ) (t : ℂ) (ht : t ∈ U) (x : X) (hx : x ∈ K) :
      HasDerivAt (fun z => H k z x) (H (k+1) t x) t := by
    have ha := (jointParameterJet_analyticAt (hF t ht x hx) k).comp
      (f := fun z : ℂ => (z,psi x)) (analyticAt_id.prod analyticAt_const)
    convert ha.differentiableAt.hasDerivAt using 1 <;>
      simp only [H,jointParameterJet,Function.iterate_succ',Function.comp_def,parameterDeriv]
  have hstep (k : ℕ) (t : ℂ) (ht : t ∈ U) :
      HasDerivAt (fun z => ∫ x in K, w x*H k z x ∂μ)
        (∫ x in K, w x*H (k+1) t x ∂μ) t :=
    hasDerivAt_compact_bounded_weight_integral hK (hU.mem_nhds ht) (H k) (H (k+1))
      (hc k) (hc (k+1)) (hd k) w hw hB hb
  have hjet : ∀ k : ℕ, ∀ t ∈ U,
      iteratedDeriv k (fun z => ∫ x in K, w x*H 0 z x ∂μ) t =
        ∫ x in K, w x*H k t x ∂μ := by
    intro k
    induction k with
    | zero => intro t ht; rfl
    | succ k ih =>
      intro t ht
      have he : iteratedDeriv k (fun z => ∫ x in K, w x*H 0 z x ∂μ) =ᶠ[𝓝 t]
          (fun z => ∫ x in K, w x*H k z x ∂μ) :=
        Filter.Eventually.mono (hU.mem_nhds ht) (fun z hz => ih z hz)
      rw [iteratedDeriv_succ,he.deriv_eq]
      exact (hstep k t ht).deriv
  simpa only [H,jointParameterJet_eq,← iteratedDeriv_eq_iterate,iteratedDeriv_zero] using hjet j s hs

theorem compact_bounded_weight_derivatives_tendsto
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {U : Set ℂ} (hU : IsOpen U) (F : ℂ × E → ℂ) (psi : X → E) (hpsi : Continuous psi)
    (hF : ∀ s ∈ U, ∀ x ∈ K, AnalyticAt ℂ F (s,psi x))
    (w : ℕ → X → ℂ) (wlim : X → ℂ)
    (hw : ∀ k, AEStronglyMeasurable (w k) (μ.restrict K))
    (hwlim : AEStronglyMeasurable wlim (μ.restrict K))
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k, ∀ᵐ x ∂μ.restrict K, ‖w k x‖ ≤ B)
    (hblim : ∀ᵐ x ∂μ.restrict K, ‖wlim x‖ ≤ B)
    (hlim : ∀ᵐ x ∂μ.restrict K, Tendsto (fun k => w k x) atTop (𝓝 (wlim x)))
    (j : ℕ) {s : ℂ} (hs : s ∈ U) :
    Tendsto (fun k => iteratedDeriv j (fun t => ∫ x in K, w k x*F (t,psi x) ∂μ) s)
      atTop (𝓝 (iteratedDeriv j (fun t => ∫ x in K, wlim x*F (t,psi x) ∂μ) s)) := by
  let J := fun x => iteratedDeriv j (fun t => F (t,psi x)) s
  have hJ : ContinuousOn J K := by
    intro x hx
    have ha := (jointParameterJet_analyticAt (hF s hs x hx) j).continuousAt
    have hh := ha.comp (f := fun x => (s,psi x)) (continuous_const.prodMk hpsi).continuousAt
    simpa only [Function.comp_def,J,jointParameterJet_eq,← iteratedDeriv_eq_iterate] using hh.continuousWithinAt
  have hi : Integrable J (μ.restrict K) := hJ.integrableOn_compact hK
  have ht := tendsto_integral_of_dominated_convergence (μ := μ.restrict K)
    (fun x => B*‖J x‖)
    (fun k => (hw k).mul hi.aestronglyMeasurable) (hi.norm.const_mul B)
    (fun k => (hb k).mono (fun x hx => by
      simp only [Pi.mul_apply,norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)))
    (hlim.mono (fun x hx => hx.mul tendsto_const_nhds))
  simpa only [compact_bounded_weight_integral_iteratedDeriv hK hU F psi hpsi hF _
      (hw _) hB (hb _) j hs,
    compact_bounded_weight_integral_iteratedDeriv hK hU F psi hpsi hF wlim hwlim hB hblim j hs,J,Pi.mul_apply] using ht

end
end IsingBulk.Tail
