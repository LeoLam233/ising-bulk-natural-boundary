import IsingBulk.AnisoF002.C03.RegularEdgeLog
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform jets of the actual regular-edge logarithmic phase

One compact parameter/cosine neighborhood controls the principal logarithm.
Its finite sum is the logarithm of the complete root product, and every
fixed derivative has the required linear particle-number cost.  The mean
value estimate below gives a protected local disk for the rational site
factor without applying Cauchy estimates across a pole.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set
open scoped Topology BigOperators

structure RegularEdgePhaseControl (c a : ℂ → ℂ) where
  radius : ℝ
  cosineRadius : ℝ
  phaseBound : ℝ
  radius_pos : 0 < radius
  cosineRadius_pos : 0 < cosineRadius
  phaseBound_pos : 0 < phaseBound
  phase_analytic : ∀ t ∈ Metric.closedBall (0 : ℂ) radius,
    ∀ v ∈ Metric.thickening cosineRadius complexCosineInterval,
      AnalyticAt ℂ (edgeJointPhase c a) (t, v)
  phase_bound : ∀ t ∈ Metric.closedBall (0 : ℂ) radius, ∀ q : ℝ,
    ‖edgeAnglePhase c a t q‖ ≤ phaseBound

theorem exists_regular_edge_phase_control {c a : ℂ → ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ c 0) (ha : AnalyticAt ℂ a 0) (hc0 : c 0 = (b : ℂ))
    (hb : |b| < 1) (ha0 : 0 < (a 0).im) :
    Nonempty (RegularEdgePhaseControl c a) := by
  obtain ⟨delta, hd, hdelta⟩ := exists_regular_edge_phase_neighborhood hc ha hc0 hb ha0
  let K : Set (ℂ × ℂ) := Metric.closedBall (0 : ℂ) delta ×ˢ complexCosineInterval
  have hK : IsCompact K := (isCompact_closedBall _ _).prod complexCosineInterval_compact
  have hcont : ContinuousOn (edgeJointPhase c a) K := by
    intro p hp
    exact (hdelta p.1 hp.1 p.2 (Metric.self_subset_thickening hd _ hp.2)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨{
    radius := delta
    cosineRadius := delta
    phaseBound := max M 0 + 1
    radius_pos := hd
    cosineRadius_pos := hd
    phaseBound_pos := by positivity
    phase_analytic := hdelta
    phase_bound := ?_ }⟩
  intro t ht q
  exact (hM (t, (Real.cos q : ℂ)) ⟨ht, real_cos_mem_complexCosineInterval q⟩).trans
    ((le_max_left _ _).trans (le_add_of_nonneg_right (by norm_num)))

namespace RegularEdgePhaseControl
variable {c a : ℂ → ℂ} (d : RegularEdgePhaseControl c a)

theorem anglePhase_parameter_analytic {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) (q : ℝ) :
    AnalyticAt ℂ (fun u => edgeAnglePhase c a u q) t :=
  (d.phase_analytic t ht _ (Metric.self_subset_thickening d.cosineRadius_pos _
    (real_cos_mem_complexCosineInterval q))).comp
      (f := fun u : ℂ => (u, (Real.cos q : ℂ))) (analyticAt_id.prod analyticAt_const)

theorem totalPhase_parameter_analytic {N : ℕ} (x : Fin N → ℝ) {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) :
    AnalyticAt ℂ (fun u => edgeTotalPhase c a u x) t := by
  exact Finset.univ.analyticAt_fun_sum fun i _ => d.anglePhase_parameter_analytic ht (x i)

theorem totalPhase_norm_le {N : ℕ} (x : Fin N → ℝ) {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) d.radius) :
    ‖edgeTotalPhase c a t x‖ ≤ (N : ℝ) * d.phaseBound := by
  calc
    ‖edgeTotalPhase c a t x‖ ≤ ∑ i, ‖edgeAnglePhase c a t (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, d.phaseBound := Finset.sum_le_sum fun i _ => d.phase_bound t ht (x i)
    _ = (N : ℝ) * d.phaseBound := by simp

theorem half_disk_subset {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2)) :
    Metric.closedBall t (d.radius / 2) ⊆ Metric.closedBall 0 d.radius := by
  apply Metric.closedBall_subset_closedBall'
  have htd := Metric.mem_closedBall.mp ht
  linarith

theorem totalPhase_jet_bound {N : ℕ} (x : Fin N → ℝ) {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2)) (j : ℕ) :
    ‖iteratedDeriv j (fun u => edgeTotalPhase c a u x) t‖ ≤
      j.factorial * ((N : ℝ) * d.phaseBound) / (d.radius / 2) ^ j := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (half_pos d.radius_pos)
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (ne_of_gt (half_pos d.radius_pos))]
    intro u hu
    exact (d.totalPhase_parameter_analytic x (d.half_disk_subset ht hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    exact d.totalPhase_norm_le x (d.half_disk_subset ht (Metric.sphere_subset_closedBall hu))

theorem totalPhase_deriv_bound {N : ℕ} (x : Fin N → ℝ) {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2)) :
    ‖deriv (fun u => edgeTotalPhase c a u x) t‖ ≤
      (N : ℝ) * (2 * d.phaseBound / d.radius) := by
  have h := d.totalPhase_jet_bound x ht 1
  simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at h
  convert h using 1
  ring

theorem totalPhase_lipschitz {N : ℕ} (x : Fin N → ℝ) {t u : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2))
    (hu : u ∈ Metric.closedBall (0 : ℂ) (d.radius / 2)) :
    ‖edgeTotalPhase c a u x - edgeTotalPhase c a t x‖ ≤
      (N : ℝ) * (2 * d.phaseBound / d.radius) * ‖u - t‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun v : ℂ => edgeTotalPhase c a v x) (x := t) (y := u)
      (C := (N : ℝ) * (2 * d.phaseBound / d.radius))
      (s := Metric.closedBall (0 : ℂ) (d.radius / 2))
  · intro v hv
    exact (d.totalPhase_parameter_analytic x (Metric.closedBall_subset_closedBall
      (half_le_self d.radius_pos.le) hv)).differentiableAt
  · intro v hv
    exact d.totalPhase_deriv_bound x hv
  · exact convex_closedBall (0 : ℂ) (d.radius / 2)
  · exact ht
  · exact hu

theorem totalPhase_real_protected {N : ℕ} (x : Fin N → ℝ) {t u : ℂ} {eta : ℝ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2))
    (hu : u ∈ Metric.closedBall (0 : ℂ) (d.radius / 2))
    (heta : eta ≤ (edgeTotalPhase c a t x).re)
    (hdist : (N : ℝ) * (2 * d.phaseBound / d.radius) * ‖u - t‖ ≤ eta / 2) :
    eta / 2 ≤ (edgeTotalPhase c a u x).re := by
  have hn := (d.totalPhase_lipschitz x ht hu).trans hdist
  have hr := (abs_le.mp (Complex.abs_re_le_norm
    (edgeTotalPhase c a u x - edgeTotalPhase c a t x))).1
  simp only [Complex.sub_re] at hr
  linarith

end RegularEdgePhaseControl
end
end IsingBulk.AnisoF002.RegularTail.C03
