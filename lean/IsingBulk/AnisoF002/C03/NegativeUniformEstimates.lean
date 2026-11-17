import IsingBulk.AnisoF002.C03.NegativePoleContraction

/-!
# Uniform local estimates for the single physical phase

The constants are obtained from analyticity of one two-variable phase.
The estimates are chosen before the number of particles and control the
actual Fréchet derivative and quadratic remainder on one complex ball.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem analytic_phase_uniform_estimates {g : ℂ × ℂ → ℂ}
    (hg : AnalyticAt ℂ g (0, 0))
    (hc : fderiv ℂ g (0, 0) (1, 0) ≠ 0) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      (∀ p ∈ Metric.ball (0, 0) r, AnalyticAt ℂ g p ∧
        ‖fderiv ℂ g p (1, 0) - fderiv ℂ g (0, 0) (1, 0)‖ ≤
          ‖fderiv ℂ g (0, 0) (1, 0)‖ / 2) ∧
      (∀ p ∈ Metric.ball (0, 0) r, ∀ q ∈ Metric.ball (0, 0) r,
        ‖fderiv ℂ g q - fderiv ℂ g p‖ ≤ M * ‖q - p‖) ∧
      ∀ p ∈ Metric.ball (0, 0) r, ∀ q ∈ Metric.ball (0, 0) r,
        ‖g q - g p - fderiv ℂ g p (q - p)‖ ≤ M * ‖q - p‖ ^ 2 := by
  let c : ℂ := fderiv ℂ g (0, 0) (1, 0)
  let M : ℝ := ‖fderiv ℂ (fderiv ℂ g) (0, 0)‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hbM : ∀ᶠ p in 𝓝 (0, 0), ‖fderiv ℂ (fderiv ℂ g) p‖ < M :=
    hg.fderiv.fderiv.continuousAt.norm.eventually
      (Iio_mem_nhds (by dsimp [M]; linarith))
  have htemp : ContinuousAt (fun p => fderiv ℂ g p (1, 0) - c) (0, 0) :=
    (hg.fderiv.continuousAt.clm_apply continuousAt_const).sub_const c
  have hbT : ∀ᶠ p in 𝓝 (0, 0), ‖fderiv ℂ g p (1, 0) - c‖ < ‖c‖ / 2 :=
    htemp.norm.eventually (Iio_mem_nhds (by
      simp only [c, sub_self, norm_zero]
      exact half_pos (norm_pos_iff.mpr hc)))
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff.mp
    (hg.eventually_analyticAt.and (hbM.and hbT))
  have hh (p : ℂ × ℂ) (hp : p ∈ Metric.ball (0, 0) r) :
      AnalyticAt ℂ g p ∧ ‖fderiv ℂ (fderiv ℂ g) p‖ ≤ M ∧
        ‖fderiv ℂ g p (1, 0) - c‖ ≤ ‖c‖ / 2 := by
    obtain ⟨ha, hm, ht⟩ := hall (Metric.mem_ball.mp hp)
    exact ⟨ha, hm.le, ht.le⟩
  have hL (p : ℂ × ℂ) (hp : p ∈ Metric.ball (0, 0) r)
      (q : ℂ × ℂ) (hq : q ∈ Metric.ball (0, 0) r) :
      ‖fderiv ℂ g q - fderiv ℂ g p‖ ≤ M * ‖q - p‖ :=
    (convex_ball (0 : ℂ × ℂ) r).norm_image_sub_le_of_norm_fderiv_le
      (fun a ha => (hh a ha).1.fderiv.differentiableAt)
      (fun a ha => (hh a ha).2.1) hp hq
  refine ⟨r, M, hr, hM, (fun p hp => ⟨(hh p hp).1, (hh p hp).2.2⟩), hL, ?_⟩
  intro p hp q hq
  have hs : segment ℝ p q ⊆ Metric.ball (0, 0) r :=
    (convex_ball (0 : ℂ × ℂ) r).segment_subset hp hq
  have hb : ∀ a ∈ segment ℝ p q,
      ‖fderiv ℂ g a - fderiv ℂ g p‖ ≤ M * ‖q - p‖ := by
    intro a ha
    exact (hL p hp a (hs ha)).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment ha) hM.le)
  have he := (convex_segment p q).norm_image_sub_le_of_norm_fderiv_le'
    (fun a ha => (hh a (hs ha)).1.differentiableAt) hb
    (left_mem_segment ℝ p q) (right_mem_segment ℝ p q)
  simpa only [pow_two, mul_assoc] using he

end
end IsingBulk.AnisoF002.NegativeHT
