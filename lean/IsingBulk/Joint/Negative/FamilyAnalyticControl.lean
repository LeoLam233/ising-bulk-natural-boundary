import IsingBulk.Joint.Negative.CompactFamilies
import IsingBulk.Joint.RegularEdges.MixedCauchy
import Mathlib.Analysis.Calculus.MeanValue

/-! # Common analytic coordinate control for compact complex families -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open scoped Topology
open IsingBulk.Joint.RegularEdges

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- Uniform control in every independent complex parameter direction, on one
ball about each point of an arbitrary compact center set. -/
theorem compact_analytic_linear_bound (H : E → G) {Q : Set E}
    (hQ : IsCompact Q) (hH : ∀ eta∈Q, AnalyticAt ℂ H eta) :
    ∃ δ L : ℝ, 0<δ ∧ 0<L ∧ ∀ eta∈Q, ∀ x∈ball eta δ,
      AnalyticAt ℂ H x ∧ ‖H x-H eta‖≤L*‖x-eta‖ := by
  obtain ⟨C,hC⟩ := hQ.exists_bound_of_continuousOn
    (fun eta heta => (hH eta heta).continuousAt.continuousWithinAt)
  let M := max C 0+1
  have hM : 0<M := by dsimp [M]; linarith [le_max_right C 0]
  let U : Set E := {q | AnalyticAt ℂ H q ∧ ‖H q‖<M}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    exact hq.1.eventually_analyticAt.and
      (hq.1.continuousAt.norm.eventually_lt continuousAt_const hq.2)
  obtain ⟨δ,hδ,hthick⟩ := hQ.exists_cthickening_subset_open hU (by
    intro eta heta
    refine ⟨hH eta heta,?_⟩
    dsimp [M]
    linarith [hC eta heta,le_max_left C 0])
  refine ⟨δ/2,4*M/δ,half_pos hδ,by positivity,?_⟩
  intro eta heta x hx
  have hall : ∀ y∈ball eta δ, AnalyticAt ℂ H y ∧ ‖H y‖<M := by
    intro y hy
    exact hthick (mem_cthickening_of_dist_le y eta δ Q heta (le_of_lt hy))
  have hsub : ball eta (δ/2)⊆ball eta δ := ball_subset_ball (by linarith)
  refine ⟨(hall x (hsub hx)).1,?_⟩
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hall z (hsub hz)).1.differentiableAt) ?_
    (convex_ball eta (δ/2)) (mem_ball_self (half_pos hδ)) hx
  intro z hz
  have hj := norm_iteratedFDeriv_le_on_half_ball 1 hδ hM.le
    (fun z hz => (hall z hz).1) (fun z hz => (hall z hz).2.le) hz
  rw [norm_iteratedFDeriv_one] at hj
  convert hj using 1
  norm_num
  ring

/-- Joint analyticity near a compact complex family constructs a single
transverse Lipschitz constant. No derivative bound is supplied as a premise. -/
theorem compact_family_analytic_linear_bound (H : ℂ × E → G) {Q : Set E}
    (hQ : IsCompact Q) (hH : ∀ eta∈Q, AnalyticAt ℂ H (0,eta)) :
    ∃ δ L : ℝ, 0<δ ∧ 0<L ∧ ∀ eta∈Q, ∀ t : ℂ, ‖t‖<δ →
      AnalyticAt ℂ (fun t => H (t,eta)) t ∧
      ‖H (t,eta)-H (0,eta)‖≤L*‖t‖ := by
  have hcont : ContinuousOn (fun eta => H (0,eta)) Q := by
    intro eta heta
    exact ((hH eta heta).continuousAt.comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := hQ.exists_bound_of_continuousOn hcont
  let M := max C 0+1
  have hM : 0<M := by dsimp [M]; linarith [le_max_right C 0]
  let U : Set (ℂ × E) := {q | AnalyticAt ℂ H q ∧ ‖H q‖<M}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    exact hq.1.eventually_analyticAt.and
      (hq.1.continuousAt.norm.eventually_lt continuousAt_const hq.2)
  obtain ⟨δ,hδ,htube⟩ := compact_product_tube hQ hU (by
    intro eta heta
    refine ⟨hH eta heta,?_⟩
    dsimp [M]
    linarith [hC eta heta,le_max_left C 0])
  refine ⟨δ/2,4*M/δ,half_pos hδ,by positivity,?_⟩
  intro eta heta t ht
  have ha : AnalyticOnNhd ℂ (fun t => H (t,eta)) (ball 0 δ) := by
    intro t ht
    exact (htube eta heta t (by simpa using ht)).1.comp (f := fun t : ℂ => (t,eta))
      (analyticAt_id.prod analyticAt_const)
  have hn : ∀ t∈ball (0:ℂ) δ, ‖H (t,eta)‖≤M := by
    intro t ht
    exact (htube eta heta t (by simpa using ht)).2.le
  have hsub : ball (0:ℂ) (δ/2)⊆ball 0 δ := ball_subset_ball (by linarith)
  have ht' : t∈ball (0:ℂ) (δ/2) := by simpa using ht
  refine ⟨ha t (hsub ht'),?_⟩
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (ha z (hsub hz)).differentiableAt)
    (C := 4*M/δ) (by
      intro z hz
      have hj := norm_iteratedFDeriv_le_on_half_ball 1 hδ hM.le ha hn hz
      rw [norm_iteratedFDeriv_one] at hj
      convert hj using 1
      norm_num
      ring)
    (convex_ball (0:ℂ) (δ/2)) (mem_ball_self (half_pos hδ)) ht'
  simpa only [sub_zero] using hh

end
end IsingBulk.Joint.Negative
