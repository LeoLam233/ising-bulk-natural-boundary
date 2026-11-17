import IsingBulk.AnisoF002.C03.NegativeAllAnglePoleAnalytic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Schwarz

/-!
# Uniform factorization at every inner phase pole

The divided difference fills the zero of the actual normalized phase.
The derivative estimate on the common convex temperature disk controls
this factor, including its value at the pole; no punctured-disk bound or
unproved analytic quotient is assumed.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology

theorem dslope_close_of_deriv_close {F : ℂ → ℂ} {a T t : ℂ} {R ε : ℝ}
    (hd : ∀ u ∈ Metric.closedBall (0 : ℂ) R, DifferentiableAt ℂ F u)
    (hclose : ∀ u ∈ Metric.closedBall (0 : ℂ) R, ‖deriv F u - a‖ ≤ ε)
    (hT : T ∈ Metric.closedBall (0 : ℂ) R)
    (ht : t ∈ Metric.closedBall (0 : ℂ) R) :
    ‖dslope F T t - a‖ ≤ ε := by
  rcases eq_or_ne t T with rfl | hne
  · simpa only [dslope_same] using hclose t ht
  let G : ℂ → ℂ := fun u => F u - a * u
  have hG (u : ℂ) (hu : u ∈ Metric.closedBall (0 : ℂ) R) :
      HasDerivAt G (deriv F u - a) u := by
    have hlin : HasDerivAt (fun v : ℂ => a * v) a u := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul a
    exact (hd u hu).hasDerivAt.fun_sub hlin
  have hb := (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hG u hu).hasDerivWithinAt) hclose hT ht
  have he : (t - T) * (dslope F T t - a) = G t - G T := by
    have hh := sub_smul_dslope F T t
    simp only [smul_eq_mul] at hh
    dsimp [G]
    linear_combination hh
  rw [← he, norm_mul] at hb
  have hnorm : 0 < ‖t - T‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  nlinarith

theorem analyticOnNhd_dslope_ball {F : ℂ → ℂ} {T : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) R))
    (hT : T ∈ Metric.ball (0 : ℂ) R) :
    AnalyticOnNhd ℂ (dslope F T) (Metric.ball (0 : ℂ) R) := by
  apply (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).mpr
  exact (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds hT)).mpr
    hF.differentiableOn

theorem phase_factor_uniform {F : ℂ → ℂ} {a T : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hF : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) R))
    (hclose : ∀ u ∈ Metric.closedBall (0 : ℂ) R, ‖deriv F u - a‖ ≤ ‖a‖ / 2)
    (hT : T ∈ Metric.ball (0 : ℂ) R) (hzero : F T = 0) :
    AnalyticOnNhd ℂ (dslope F T) (Metric.ball (0 : ℂ) R) ∧
      ∀ t ∈ Metric.closedBall (0 : ℂ) R,
        F t = (t - T) * dslope F T t ∧
        ‖dslope F T t - a‖ ≤ ‖a‖ / 2 ∧
        ‖a‖ / 2 ≤ ‖dslope F T t‖ ∧
        ‖dslope F T t‖ ≤ 3 * ‖a‖ / 2 ∧
        dslope F T t ≠ 0 := by
  refine ⟨analyticOnNhd_dslope_ball (hF.mono Metric.ball_subset_closedBall) hT, ?_⟩
  intro t ht
  have hclose' := dslope_close_of_deriv_close
    (fun u hu => (hF u hu).differentiableAt) hclose (Metric.ball_subset_closedBall hT) ht
  have he : F t = (t - T) * dslope F T t := by
    simpa only [hzero, sub_zero, smul_eq_mul] using (sub_smul_dslope F T t).symm
  have hlow : ‖a‖ / 2 ≤ ‖dslope F T t‖ := by
    have hh := norm_sub_le_norm_sub_add_norm_sub a (dslope F T t) 0
    simp only [sub_zero, norm_sub_rev a] at hh
    linarith
  have hupp : ‖dslope F T t‖ ≤ 3 * ‖a‖ / 2 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (dslope F T t) a 0
    simp only [sub_zero] at hh
    linarith
  refine ⟨he, hclose', hlow, hupp, ?_⟩
  exact norm_pos_iff.mp ((half_pos (norm_pos_iff.mpr ha)).trans_le hlow)

end
end IsingBulk.AnisoF002.NegativeHT
