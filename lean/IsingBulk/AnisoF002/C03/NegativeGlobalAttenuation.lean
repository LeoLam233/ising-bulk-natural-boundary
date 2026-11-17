import IsingBulk.AnisoF002.C03.NegativeGlobalPhase

/-!
# Actual inward attenuation on the whole negative-edge angular circle

The negative physical parameter is t=-epsilon.  On every shortest real
angular lift the genuine logarithmic phase has a lower bound proportional
to epsilon+q², including epsilon=0.  The control is constructed from B,
on one disk before the particle number.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem upper_phase_real_lower_of_region {W : ℂ} {L : ℝ}
    (hW : upperEdgeRegion W) (hL : ‖upperEdgePhase W‖ ≤ L) :
    W.im / Real.exp L ≤ (upperEdgePhase W).re := by
  rcases hW with hpos | hreal
  · exact upperEdgePhase_re_ge_im_div_exp hpos hL
  · rw [hreal.1, zero_div]
    exact upperEdgePhase_re_nonneg (Or.inr hreal)

theorem negative_global_dispersion_im (B : ℂ → ℂ) (φ eps q : ℝ) :
    (localNegativeDispersion B φ (-(eps : ℂ), (q : ℂ))).im =
      -(B (-(eps : ℂ))).im * (eps + 1 - Real.cos q) := by
  unfold localNegativeDispersion
  rw [← Complex.ofReal_cos]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.one_re,
    Complex.sub_im, Complex.neg_im, Complex.one_im, neg_zero, sub_self,
    mul_zero, zero_add]
  ring

theorem negative_global_dispersion_region {B : ℂ → ℂ} {φ eps q : ℝ}
    (hφ : 0 < φ) (hπ : φ < Real.pi) (heps : 0 ≤ eps)
    (hB : (B (-(eps : ℂ))).im < 0) :
    upperEdgeRegion (localNegativeDispersion B φ (-(eps : ℂ), (q : ℂ))) := by
  have hX : 0 ≤ eps + 1 - Real.cos q := by linarith [Real.cos_le_one q]
  by_cases hp : 0 < eps + 1 - Real.cos q
  · left
    rw [negative_global_dispersion_im]
    exact mul_pos (neg_pos.mpr hB) hp
  · have hz : eps + 1 - Real.cos q = 0 := le_antisymm (le_of_not_gt hp) hX
    have he : localNegativeDispersion B φ (-(eps : ℂ), (q : ℂ)) = (Real.cos φ : ℂ) := by
      unfold localNegativeDispersion
      rw [← Complex.ofReal_cos]
      have hzero : -(eps : ℂ) - (1 - (Real.cos q : ℂ)) = 0 := by
        exact_mod_cast (show -eps - (1 - Real.cos q) = 0 by linarith)
      rw [hzero, mul_zero, add_zero]
    rw [he]
    right
    refine ⟨by simp, ?_⟩
    simpa only [Complex.ofReal_re] using abs_cos_lt_one_of_sin_ne_zero
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ hπ))

set_option maxHeartbeats 1000000 in
theorem exists_negative_global_inward_attenuation {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0) :
    ∃ d : RegularEdgePhaseControl (negativeGlobalCenter B φ) (negativeGlobalCoefficient B),
      ∃ eps0 kappa : ℝ, 0 < eps0 ∧ 0 < kappa ∧
        ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps0 →
          (-(eps : ℂ) ∈ Metric.closedBall (0 : ℂ) (d.radius / 4) ∧
            ∀ q : ℝ, |q| ≤ Real.pi →
              kappa * (eps + q ^ 2) ≤ (negativeGlobalPhase B φ (-(eps : ℂ), (q : ℂ))).re) := by
  obtain ⟨d⟩ := (exists_negative_global_controls hB hφ hπ hBi).2
  let a0 : ℝ := -(B 0).im
  have ha0 : 0 < a0 := neg_pos.mpr hBi
  have hcoeff : ∀ᶠ t : ℂ in 𝓝 0, a0 / 2 < -(B t).im :=
    ((Complex.continuous_im.continuousAt.comp hB.continuousAt).neg).eventually
      (Ioi_mem_nhds (half_lt_self ha0))
  obtain ⟨r, hr, hcoeffr⟩ := Metric.eventually_nhds_iff.mp hcoeff
  let eps0 : ℝ := min (r / 2) (d.radius / 4)
  let alpha : ℝ := min (a0 / 2) (a0 / Real.pi ^ 2)
  let kappa : ℝ := alpha / Real.exp d.phaseBound
  have heps0 : 0 < eps0 := lt_min (half_pos hr) (div_pos d.radius_pos (by norm_num))
  have halpha : 0 < alpha := lt_min (half_pos ha0) (div_pos ha0 (sq_pos_of_pos Real.pi_pos))
  have hkappa : 0 < kappa := div_pos halpha (Real.exp_pos _)
  refine ⟨d, eps0, kappa, heps0, hkappa, ?_⟩
  intro eps he he0
  have hnorm : ‖-(eps : ℂ)‖ = eps := by
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg he]
  have hte : -(eps : ℂ) ∈ Metric.closedBall (0 : ℂ) (d.radius / 4) := by
    rw [Metric.mem_closedBall, dist_zero_right, hnorm]
    exact he0.trans (min_le_right _ _)
  have htr : dist (-(eps : ℂ)) 0 < r := by
    rw [dist_zero_right, hnorm]
    exact (he0.trans (min_le_left _ _)).trans_lt (half_lt_self hr)
  have hamin : a0 / 2 ≤ -(B (-(eps : ℂ))).im := (hcoeffr htr).le
  have haeps : (B (-(eps : ℂ))).im < 0 := by linarith
  refine ⟨hte, ?_⟩
  intro q hq
  have hbound := d.phase_bound (-(eps : ℂ))
    (Metric.closedBall_subset_closedBall (by linarith [d.radius_pos]) hte) q
  rw [← negativeGlobalPhase_real] at hbound
  have hphase := upper_phase_real_lower_of_region
    (negative_global_dispersion_region hφ hπ he haeps) hbound
  have hcos : 0 ≤ 1 - Real.cos q := sub_nonneg.mpr (Real.cos_le_one q)
  have hcosquad : 2 / Real.pi ^ 2 * q ^ 2 ≤ 1 - Real.cos q := by
    linarith [Real.cos_le_one_sub_mul_cos_sq hq]
  have himlower : alpha * (eps + q ^ 2) ≤
      -(B (-(eps : ℂ))).im * (eps + 1 - Real.cos q) := by
    have hcprod := mul_le_mul_of_nonneg_left hcosquad (half_pos ha0).le
    have hamul := mul_le_mul_of_nonneg_right hamin (show 0 ≤ eps + 1 - Real.cos q by linarith)
    have ha1 : alpha ≤ a0 / 2 := min_le_left _ _
    have haq : alpha ≤ a0 / Real.pi ^ 2 := min_le_right _ _
    have heprod := mul_le_mul_of_nonneg_right ha1 he
    have hqprod := mul_le_mul_of_nonneg_right haq (sq_nonneg q)
    have hid : a0 / 2 * (2 / Real.pi ^ 2 * q ^ 2) = a0 / Real.pi ^ 2 * q ^ 2 := by ring
    rw [hid] at hcprod
    nlinarith
  calc
    kappa * (eps + q ^ 2) = alpha * (eps + q ^ 2) / Real.exp d.phaseBound := by
      dsimp [kappa]
      ring
    _ ≤ (-(B (-(eps : ℂ))).im * (eps + 1 - Real.cos q)) / Real.exp d.phaseBound :=
      div_le_div_of_nonneg_right himlower (Real.exp_pos _).le
    _ ≤ _ := by simpa only [negative_global_dispersion_im, negativeGlobalPhase] using hphase

end
end IsingBulk.AnisoF002.NegativeHT
