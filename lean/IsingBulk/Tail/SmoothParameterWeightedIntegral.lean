import IsingBulk.Tail.BoundedWeightAnalyticIntegral
import IsingBulk.Tail.ParameterSmoothLie

/-! Differentiation and bounded-weight limits with real angular smoothness.
The angular factors require no complex analytic extension. -/
namespace IsingBulk.Tail
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ParameterSmoothOn.iteratedDeriv {Ω : Set (ℂ × E)} (hΩ : IsOpen Ω)
    {F : ℂ → E → ℂ} (hF : ParameterSmoothOn Ω F) (j : ℕ) :
    ParameterSmoothOn Ω (fun s x => iteratedDeriv j (fun t => F t x) s) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hF
  | succ j ih => simpa only [iteratedDeriv_succ] using ih.paramDeriv hΩ

variable [MeasurableSpace E] [BorelSpace E]

theorem smooth_parameter_bounded_weight_integral_iteratedDeriv
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {K : Set E} (hK : IsCompact K)
    {Ω : Set (ℂ × E)} (hΩ : IsOpen Ω) {U : Set ℂ} (hU : IsOpen U)
    (F : ℂ → E → ℂ) (hF : ParameterSmoothOn Ω F) (hUK : U ×ˢ K ⊆ Ω)
    (w : E → ℂ) (hw : AEStronglyMeasurable w (μ.restrict K))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ.restrict K, ‖w x‖ ≤ B)
    (j : ℕ) {s : ℂ} (hs : s ∈ U) :
    iteratedDeriv j (fun t => ∫ x in K, w x*F t x ∂μ) s =
      ∫ x in K, w x*iteratedDeriv j (fun t => F t x) s ∂μ := by
  let H := fun k t x => iteratedDeriv k (fun z => F z x) t
  have hreg (k : ℕ) := hF.iteratedDeriv hΩ k
  have hc (k : ℕ) : ContinuousOn (fun z : ℂ × E => H k z.1 z.2) (U ×ˢ K) :=
    fun z hz => (hreg k z (hUK hz)).1.continuousAt.continuousWithinAt
  have hd (k : ℕ) (t : ℂ) (ht : t ∈ U) (x : E) (hx : x ∈ K) :
      HasDerivAt (fun z => H k z x) (H (k+1) t x) t := by
    simpa only [H,iteratedDeriv_succ] using (hreg k (t,x) (hUK ⟨ht,hx⟩)).2.hasDerivAt
  have hstep (k : ℕ) (t : ℂ) (ht : t ∈ U) :
      HasDerivAt (fun z => ∫ x in K, w x*H k z x ∂μ)
        (∫ x in K, w x*H (k+1) t x ∂μ) t :=
    hasDerivAt_compact_bounded_weight_integral hK (hU.mem_nhds ht) (H k) (H (k+1))
      (hc k) (hc (k+1)) (hd k) w hw hB hb
  have hj : ∀ k : ℕ, ∀ t ∈ U,
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
  simpa only [H,iteratedDeriv_zero] using hj j s hs

theorem smooth_parameter_bounded_weight_derivatives_tendsto
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ] {K : Set E} (hK : IsCompact K)
    {Ω : Set (ℂ × E)} (hΩ : IsOpen Ω) {U : Set ℂ} (hU : IsOpen U)
    (F : ℂ → E → ℂ) (hF : ParameterSmoothOn Ω F) (hUK : U ×ˢ K ⊆ Ω)
    (w : ℕ → E → ℂ) (wlim : E → ℂ)
    (hw : ∀ k, AEStronglyMeasurable (w k) (μ.restrict K))
    (hwlim : AEStronglyMeasurable wlim (μ.restrict K))
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k, ∀ᵐ x ∂μ.restrict K, ‖w k x‖ ≤ B)
    (hblim : ∀ᵐ x ∂μ.restrict K, ‖wlim x‖ ≤ B)
    (hlim : ∀ᵐ x ∂μ.restrict K, Tendsto (fun k => w k x) atTop (𝓝 (wlim x)))
    (j : ℕ) {s : ℂ} (hs : s ∈ U) :
    Tendsto (fun k => iteratedDeriv j (fun t => ∫ x in K, w k x*F t x ∂μ) s)
      atTop (𝓝 (iteratedDeriv j (fun t => ∫ x in K, wlim x*F t x ∂μ) s)) := by
  let J := fun x => iteratedDeriv j (fun t => F t x) s
  have hJ : ContinuousOn J K := by
    intro x hx
    have hc := (hF.iteratedDeriv hΩ j (s,x) (hUK ⟨hs,hx⟩)).1.continuousAt
    exact (hc.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hi : Integrable J (μ.restrict K) := hJ.integrableOn_compact hK
  have ht := tendsto_integral_of_dominated_convergence (μ := μ.restrict K)
    (fun x => B*‖J x‖)
    (fun k => (hw k).mul hi.aestronglyMeasurable) (hi.norm.const_mul B)
    (fun k => (hb k).mono (fun x hx => by
      simp only [Pi.mul_apply,norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)))
    (hlim.mono (fun x hx => hx.mul tendsto_const_nhds))
  simpa only [smooth_parameter_bounded_weight_integral_iteratedDeriv hK hΩ hU F hF hUK _
      (hw _) hB (hb _) j hs,
    smooth_parameter_bounded_weight_integral_iteratedDeriv hK hΩ hU F hF hUK wlim hwlim hB hblim j hs,
    J,Pi.mul_apply] using ht

end
end IsingBulk.Tail
