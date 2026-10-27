import IsingBulk.Preferred22.LiftedStokes
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Differentiation of a genuinely smooth compact angular integral. This
lemma is used only for each fixed physical puncture; it makes no tail or
uniform-in-puncture smoothness assumption. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory Metric
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The parameter derivative of a smooth function on a compact angular
set can be integrated, with domination proved by joint compactness. -/
theorem preferred_compact_radial_integral_hasDerivAt {n : ℕ}
    (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (F : ℝ × (Fin n → ℝ) → ℂ) {a b t : ℝ} (ht : t∈Ioo a b)
    (hF : ∀ u∈Ioo a b,∀ x∈K,ContDiffAt ℝ ∞ F (u,x)) :
    HasDerivAt (fun u : ℝ => ∫ x in K,F (u,x))
      (∫ x in K,fderiv ℝ F (t,x) (1,0)) t := by
  let H := fun z : ℝ × (Fin n → ℝ) => fderiv ℝ F z (1,0)
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (isOpen_Ioo.mem_nhds ht)
  let S := Metric.ball t (r/2)
  have hclosed (u : ℝ) (hu : u∈Metric.closedBall t (r/2)) : u∈Ioo a b :=
    hrsub (show u∈Metric.ball t r from (mem_closedBall.mp hu).trans_lt (half_lt_self hr))
  have hS (u : ℝ) (hu : u∈S) : u∈Ioo a b := hclosed u (Metric.ball_subset_closedBall hu)
  have hH (u : ℝ) (hu : u∈Ioo a b) (x : Fin n → ℝ) (hx : x∈K) :
      ContDiffAt ℝ ∞ H (u,x) :=
    ((hF u hu x hx).fderiv_right (by simp : (∞:ℕ∞ω)+1≤∞)).clm_apply contDiffAt_const
  have hcompact : IsCompact ((Metric.closedBall t (r/2)) ×ˢ K) :=
    (isCompact_closedBall t (r/2)).prod hK
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuousOn
    (fun z hz => (hH z.1 (hclosed z.1 hz.1) z.2 hz.2).continuousAt.continuousWithinAt)
  have hFi (u : ℝ) (hu : u∈Ioo a b) : IntegrableOn (fun x => F (u,x)) K := by
    have hc : ContinuousOn (fun x => F (u,x)) K := by
      intro x hx
      exact ((hF u hu x hx).continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
    exact hc.integrableOn_compact hK
  have hHi : IntegrableOn (fun x => H (t,x)) K := by
    have hc : ContinuousOn (fun x => H (t,x)) K := by
      intro x hx
      exact ((hH t ht x hx).continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
    exact hc.integrableOn_compact hK
  have hd (u : ℝ) (hu : u∈Ioo a b) (x : Fin n → ℝ) (hx : x∈K) :
      HasDerivAt (fun v : ℝ => F (v,x)) (H (u,x)) u := by
    exact ((hF u hu x hx).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id' u).prodMk (hasDerivAt_const u x))
  have hs : S∈𝓝 t := Metric.ball_mem_nhds t (half_pos hr)
  have hmeas : ∀ᶠ u in 𝓝 t,AEStronglyMeasurable (fun x => F (u,x)) (volume.restrict K) := by
    filter_upwards [hs] with u hu
    exact (hFi u (hS u hu)).aestronglyMeasurable
  have hbound : ∀ᵐ x : Fin n → ℝ ∂volume.restrict K,∀ u∈S,‖H (u,x)‖≤C := by
    apply ae_restrict_of_forall_mem hK.measurableSet
    intro x hx u hu
    exact hC (u,x) ⟨Metric.ball_subset_closedBall hu,hx⟩
  have hdiff : ∀ᵐ x : Fin n → ℝ ∂volume.restrict K,∀ u∈S,
      HasDerivAt (fun v : ℝ => F (v,x)) (H (u,x)) u := by
    apply ae_restrict_of_forall_mem hK.measurableSet
    intro x hx u hu
    exact hd u (hS u hu) x hx
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas (hFi t ht)
    hHi.aestronglyMeasurable hbound
    ((continuousOn_const : ContinuousOn (fun _ : Fin n → ℝ => C) K).integrableOn_compact hK)
    hdiff).2

end
end IsingBulk.Preferred22
