import IsingBulk.AnisoF002.C03.IsotropicPeriodicCurrentIntegral
import IsingBulk.AnisoF002.C03.RegularCompactIntegral

/-!
# Differentiating the actual smooth finite angular integral

Joint C1 regularity on a compact angular support constructs its own
common time interval and integrable derivative bound. This applies to
the real homotopy parameter without analytically extending any cutoff.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Filter Metric MeasureTheory
open IsingBulk.AnisoF002.RegularTail.C03

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [MeasurableSpace X] [BorelSpace X] in
theorem joint_C1_compact_parameter_interval {f : ℝ × E → ℂ} {g : X → E}
    {K : Set X} {t : ℝ} (hK : IsCompact K) (hg : Continuous g)
    (hf : ∀ x ∈ K, ContDiffAt ℝ 1 f (t, g x)) :
    ∃ r : ℝ, 0 < r ∧ ∀ u ∈ closedBall t r, ∀ x ∈ K,
      ContDiffAt ℝ 1 f (u, g x) := by
  have hm : Continuous (fun p : ℝ × X => (p.1, g p.2)) :=
    continuous_fst.prodMk (hg.comp continuous_snd)
  have hU : IsOpen {p : ℝ × E | ContDiffAt ℝ 1 f p} := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    change ContDiffAt ℝ 1 f p at hp
    exact hp.eventually (by norm_num)
  have ho : IsOpen {p : ℝ × X | ContDiffAt ℝ 1 f (p.1, g p.2)} := hU.preimage hm
  have hs : ({t} : Set ℝ) ×ˢ K ⊆ {p : ℝ × X | ContDiffAt ℝ 1 f (p.1, g p.2)} := by
    rintro p ⟨hp, hx⟩
    change ContDiffAt ℝ 1 f (p.1, g p.2)
    rw [mem_singleton_iff.mp hp]
    exact hf p.2 hx
  obtain ⟨r, hr, hsub⟩ := (isCompact_singleton.prod hK).exists_cthickening_subset_open ho hs
  refine ⟨r, hr, ?_⟩
  intro u hu x hx
  apply hsub (a := (u, x))
  apply mem_cthickening_of_dist_le (u, x) (t, x) r (({t} : Set ℝ) ×ˢ K) ⟨by simp, hx⟩
  simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg : 0 ≤ dist u t)] using
    mem_closedBall.mp hu

def realParameterPartial (f : ℝ × E → ℂ) (p : ℝ × E) : ℂ :=
  fderiv ℝ f p (1, 0)

omit [MeasurableSpace X] [BorelSpace X] in
theorem realParameterPartial_continuousAt {f : ℝ × E → ℂ} {p : ℝ × E}
    (hf : ContDiffAt ℝ 1 f p) : ContinuousAt (realParameterPartial f) p :=
  (hf.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const

omit [MeasurableSpace X] [BorelSpace X] in
theorem realParameterPartial_hasDerivAt {f : ℝ × E → ℂ} {p : ℝ × E}
    (hf : ContDiffAt ℝ 1 f p) :
    HasDerivAt (fun u : ℝ => f (u, p.2)) (realParameterPartial f p) p.1 := by
  have hline : HasDerivAt (fun u : ℝ => (u, p.2)) (1, 0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact (hf.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt p.1 hline

theorem integral_hasDerivAt_of_joint_C1 {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℝ × E → ℂ} {g : X → E} {K : Set X} {t : ℝ}
    (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K) (hg : Continuous g)
    (hf : ∀ x ∈ K, ContDiffAt ℝ 1 f (t, g x)) :
    Integrable (fun x => realParameterPartial f (t, g x)) μ ∧
      HasDerivAt (fun u : ℝ => ∫ x, f (u, g x) ∂μ)
        (∫ x, realParameterPartial f (t, g x) ∂μ) t := by
  obtain ⟨r, hr, hnear⟩ := joint_C1_compact_parameter_interval hK hg hf
  let F : ℝ → X → ℂ := fun u x => f (u, g x)
  let F' : ℝ → X → ℂ := fun u x => realParameterPartial f (u, g x)
  have hm : Continuous (fun p : ℝ × X => (p.1, g p.2)) :=
    continuous_fst.prodMk (hg.comp continuous_snd)
  have h0 (u : ℝ) (hu : u ∈ closedBall t r) : ContinuousOn (F u) K := by
    intro x hx
    exact ((hnear u hu x hx).continuousAt.comp
      (f := fun y : X => (u, g y)) (continuousAt_const.prodMk hg.continuousAt)).continuousWithinAt
  have h1 : ContinuousOn (fun p : ℝ × X => F' p.1 p.2) (closedBall t r ×ˢ K) := by
    intro p hp
    exact ((realParameterPartial_continuousAt (hnear p.1 hp.1 p.2 hp.2)).comp
      (f := fun q : ℝ × X => (q.1, g q.2)) hm.continuousAt).continuousWithinAt
  have ht : t ∈ closedBall t r := mem_closedBall_self hr.le
  have h1t : ContinuousOn (F' t) K := by
    intro x hx
    exact ((realParameterPartial_continuousAt (hf x hx)).comp
      (f := fun y : X => (t, g y)) (continuousAt_const.prodMk hg.continuousAt)).continuousWithinAt
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t r).prod hK).exists_bound_of_continuousOn h1
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (s := closedBall t r) (bound := fun _ => M) (closedBall_mem_nhds t hr)
  · filter_upwards [closedBall_mem_nhds t hr] with u hu
    exact (integrable_of_carried_compact hK hμ (h0 u hu)).aestronglyMeasurable
  · exact integrable_of_carried_compact hK hμ (h0 t ht)
  · exact (integrable_of_carried_compact hK hμ h1t).aestronglyMeasurable
  · exact hμ.mono fun x hx u hu => hM (u, x) ⟨hu, hx⟩
  · exact integrable_const M
  · exact hμ.mono fun x hx u hu => realParameterPartial_hasDerivAt (hnear u hu x hx)

end IsingBulk.AnisoF002.Isotropic
