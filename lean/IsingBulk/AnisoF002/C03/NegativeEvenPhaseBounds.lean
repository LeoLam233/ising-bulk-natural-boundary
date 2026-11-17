import IsingBulk.AnisoF002.C03.NegativeAnalyticLogs

/-!
# Uniform variation of the actual even phase

The small angular derivative is derived from evenness of the single
analytic phase.  The resulting bound keeps the center angle explicitly;
at d_n = pi/n it gives the square-root error in the complete density log.
No particle-dependent analytic neighborhood is introduced.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem even_phase_angular_derivative_zero {g : ℂ × ℂ → ℂ} {t : ℂ}
    (hg : DifferentiableAt ℂ g (t, 0))
    (heven : ∀ a d : ℂ, g (a, -d) = g (a, d)) :
    fderiv ℂ g (t, 0) (0, 1) = 0 := by
  have hd : HasDerivAt (fun d : ℂ => g (t, d))
      (fderiv ℂ g (t, 0) (0, 1)) 0 :=
    hg.hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const (0 : ℂ) t).prodMk (hasDerivAt_id (0 : ℂ)))
  rw [← hd.deriv]
  exact deriv_zero_of_even hd.differentiableAt (heven t)

theorem exists_uniform_even_phase_variation {g : ℂ × ℂ → ℂ}
    (hg : AnalyticAt ℂ g (0, 0))
    (hc : fderiv ℂ g (0, 0) (1, 0) ≠ 0)
    (heven : ∀ t d : ℂ, g (t, -d) = g (t, d)) :
    ∃ r K : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < K ∧
      AnalyticOnNhd ℂ g (Metric.ball (0, 0) r) ∧
      ∀ τ d t v : ℂ, (τ, d) ∈ Metric.ball (0, 0) r →
        (t, d + v) ∈ Metric.ball (0, 0) r → ‖t - τ‖ ≤ 1 →
        ‖g (t, d + v) - g (τ, d)‖ ≤
          K * (‖t - τ‖ + ‖d‖ * ‖v‖ + ‖v‖ ^ 2) := by
  obtain ⟨s, M, hs, hM, ha, hLip, hQuad⟩ := analytic_phase_uniform_estimates hg hc
  let r : ℝ := min s 1
  let K : ℝ := ‖fderiv ℂ g (0, 0)‖ + 2 * M + 1
  have hr : 0 < r := lt_min hs zero_lt_one
  have hrs : Metric.ball (0 : ℂ × ℂ) r ⊆ Metric.ball 0 s :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hr1 : r ≤ 1 := min_le_right _ _
  have hK : 0 < K := by dsimp [K]; positivity
  have ha' : AnalyticOnNhd ℂ g (Metric.ball (0, 0) r) := fun p hp => (ha p (hrs hp)).1
  refine ⟨r, K, hr, hr1, hK, ha', ?_⟩
  intro τ d t v hp hq hu
  have hp0 : (τ, (0 : ℂ)) ∈ Metric.ball (0, 0) r := by
    simpa only [Metric.mem_ball, dist_eq_norm, Prod.mk_sub_mk, sub_zero,
      Prod.norm_def, norm_zero, max_eq_left (norm_nonneg τ)] using
      lt_of_le_of_lt (le_max_left ‖τ‖ ‖d‖)
        (by simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def] using hp : max ‖τ‖ ‖d‖ < r)
  have hzero := even_phase_angular_derivative_zero (ha' (τ, 0) hp0).differentiableAt heven
  have he : ‖fderiv ℂ g (τ, d) (0, 1)‖ ≤ M * ‖d‖ := by
    have hb := (ContinuousLinearMap.le_opNorm
      (fderiv ℂ g (τ, d) - fderiv ℂ g (τ, 0)) ((0, 1) : ℂ × ℂ))
    simp only [sub_apply, hzero, sub_zero, Prod.norm_def,
      norm_zero, norm_one, zero_le_one, max_eq_right, mul_one] at hb
    exact hb.trans (by simpa [Prod.norm_def] using hLip (τ, 0) (hrs hp0) (τ, d) (hrs hp))
  have hfd : ‖fderiv ℂ g (τ, d)‖ ≤ ‖fderiv ℂ g (0, 0)‖ + M := by
    have hb := norm_le_norm_add_norm_sub (fderiv ℂ g (0, 0)) (fderiv ℂ g (τ, d))
    rw [norm_sub_rev (fderiv ℂ g (0, 0)) (fderiv ℂ g (τ, d))] at hb
    have hl := hLip (0, 0) (Metric.mem_ball_self hs) (τ, d) (hrs hp)
    have hpn : ‖(τ, d) - (0, 0)‖ ≤ 1 :=
      by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hp).le.trans hr1
    have hm := mul_le_mul_of_nonneg_left hpn hM.le
    linarith
  have hc' : ‖fderiv ℂ g (τ, d) (1, 0)‖ ≤ ‖fderiv ℂ g (0, 0)‖ + M := by
    have hh : ‖fderiv ℂ g (τ, d) (1, 0)‖ ≤ ‖fderiv ℂ g (τ, d)‖ := by
      simpa [Prod.norm_def] using (fderiv ℂ g (τ, d)).le_opNorm ((1, 0) : ℂ × ℂ)
    exact hh.trans hfd
  have hd : (t, d + v) - (τ, d) = (t - τ) • ((1, 0) : ℂ × ℂ) + v • ((0, 1) : ℂ × ℂ) := by
    ext <;> simp
  have hlin : ‖fderiv ℂ g (τ, d) ((t, d + v) - (τ, d))‖ ≤
      (‖fderiv ℂ g (0, 0)‖ + M) * ‖t - τ‖ + M * ‖d‖ * ‖v‖ := by
    rw [hd, map_add, map_smul, map_smul]
    exact (norm_add_le _ _).trans (by
      simp only [norm_smul]
      nlinarith [mul_le_mul_of_nonneg_left hc' (norm_nonneg (t - τ)),
        mul_le_mul_of_nonneg_left he (norm_nonneg v)])
  have hnorm : ‖(t, d + v) - (τ, d)‖ ^ 2 ≤ ‖t - τ‖ ^ 2 + ‖v‖ ^ 2 := by
    simp only [Prod.mk_sub_mk, add_sub_cancel_left, Prod.norm_def]
    rcases le_total ‖t - τ‖ ‖v‖ with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg ‖t - τ‖]
    · rw [max_eq_left h]; nlinarith [sq_nonneg ‖v‖]
  have hq' := hQuad (τ, d) (hrs hp) (t, d + v) (hrs hq)
  have hrem : ‖g (t, d + v) - g (τ, d) -
      fderiv ℂ g (τ, d) ((t, d + v) - (τ, d))‖ ≤ M * (‖t - τ‖ + ‖v‖ ^ 2) := by
    have hu2 : ‖t - τ‖ ^ 2 ≤ ‖t - τ‖ := by nlinarith [norm_nonneg (t - τ)]
    exact hq'.trans (mul_le_mul_of_nonneg_left (hnorm.trans (by linarith)) hM.le)
  have hsplit := norm_le_norm_add_norm_sub
    (fderiv ℂ g (τ, d) ((t, d + v) - (τ, d))) (g (t, d + v) - g (τ, d))
  rw [norm_sub_rev (fderiv ℂ g (τ, d) ((t, d + v) - (τ, d)))
    (g (t, d + v) - g (τ, d))] at hsplit
  have hK1 : ‖fderiv ℂ g (0, 0)‖ + 2 * M ≤ K := by dsimp [K]; linarith
  have hK2 : M ≤ K := by dsimp [K]; linarith [norm_nonneg (fderiv ℂ g (0, 0))]
  calc
    ‖g (t, d + v) - g (τ, d)‖ ≤
        (‖fderiv ℂ g (0, 0)‖ + 2 * M) * ‖t - τ‖ + M * (‖d‖ * ‖v‖) + M * ‖v‖ ^ 2 := by
      linarith
    _ ≤ K * ‖t - τ‖ + K * (‖d‖ * ‖v‖) + K * ‖v‖ ^ 2 := by gcongr
    _ = K * (‖t - τ‖ + ‖d‖ * ‖v‖ + ‖v‖ ^ 2) := by ring

end
end IsingBulk.AnisoF002.NegativeHT
