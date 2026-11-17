import IsingBulk.AnisoF002.C03.NegativeScalarLogData

/-!
# Assembly of all scalar factors in the full density

This applies the constructed common logarithms to every factor of the
actual filled density.  The center value is proved nonzero and no angle
coincidence is excluded from either the identity or the estimate.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.AnisoF002.Isotropic Set Filter
open scoped Topology BigOperators

theorem norm_half_difference_sq_le (a b : ℂ) :
    ‖(a - b) / 2‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have hs := norm_sub_le a b
  nlinarith [norm_nonneg (a - b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]

theorem norm_average_sub_le (a b γ : ℂ) :
    ‖(a + b) / 2 - γ‖ ≤ (‖a - γ‖ + ‖b - γ‖) / 2 := by
  rw [show (a + b) / 2 - γ = ((a - γ) + (b - γ)) / 2 by ring,
    norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)

theorem average_mem_complex_ball {a b γ : ℂ} {r : ℝ}
    (ha : a ∈ Metric.ball γ r) (hb : b ∈ Metric.ball γ r) :
    (a + b) / 2 ∈ Metric.ball γ r := by
  rw [Metric.mem_ball, dist_eq_norm] at *
  have hh := norm_average_sub_le a b γ
  linarith

theorem scalar_logs_full_density_identity {b : ℂ → ℂ} {γ : ℂ}
    (L : CompleteDensityScalarLogs b γ) {n : ℕ} (hn : 0 < n)
    {g : ℂ × ℂ → ℂ} {τ d t : ℂ} {v : Fin n → ℂ}
    (hcenter : g (τ, d) = γ)
    (hτ : τ ∈ Metric.ball 0 L.r) (ht : t ∈ Metric.ball 0 L.r)
    (hphase : ∀ i, g (t, d + v i) ∈ Metric.ball γ L.r)
    (hsinc : ∀ ij ∈ indexPairs n, (v ij.1 - v ij.2) / 2 ∈ Metric.ball 0 L.r)
    (hc : phaseTemperatureDerivative g (τ, d) ≠ 0)
    (hd : phaseTemperatureSum n g d t v / ((n : ℂ) * phaseTemperatureDerivative g (τ, d)) ∈
      Metric.ball 1 L.r) :
    filledNegativeDensityAt n b g d τ 0 ≠ 0 ∧
      filledNegativeDensityAt n b g d t v = filledNegativeDensityAt n b g d τ 0 *
        Complex.exp (fullDensityLog n g L.Lb L.Lh L.Ls L.Ld d τ t v) := by
  have hγ := (L.h_exp γ (Metric.mem_ball_self L.r_pos)).1
  have hb0 := (L.b_exp 0 (Metric.mem_ball_self L.r_pos)).1
  have hden0 : (n : ℂ) * phaseTemperatureDerivative g (τ, d) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hn.ne') hc
  constructor
  · unfold filledNegativeDensityAt
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by norm_num)
      (filledNegativeNumerator_center_ne_zero n b g d τ γ hcenter (L.b_exp τ hτ).1 hγ)))
      (by simpa only [phaseTemperatureSum_center] using hden0)
  · apply fullDensityLog_factorization hcenter
      (normalized_log_relative_factor hb0 (L.b_exp τ hτ).1 (L.b_exp τ hτ).2 (L.b_exp t ht).2)
    · intro i
      have he := (L.h_exp _ (hphase i)).2
      exact (eq_div_iff hγ).mp he |>.symm.trans (mul_comm _ _)
    · intro ij hij
      exact (L.s_exp _ (hsinc ij hij)).2.symm
    · intro ij _
      have he := (L.h_exp _ (average_mem_complex_ball (hphase ij.1) (hphase ij.2))).2
      exact (eq_div_iff hγ).mp he |>.symm.trans (mul_comm _ _)
    · exact hden0
    · exact (L.d_exp _ hd).2

theorem scalar_logs_full_density_cost {b : ℂ → ℂ} {γ : ℂ}
    (L : CompleteDensityScalarLogs b γ) {n : ℕ} {g : ℂ × ℂ → ℂ}
    {τ d t : ℂ} {v : Fin n → ℂ}
    (hτ : τ ∈ Metric.ball 0 L.r) (ht : t ∈ Metric.ball 0 L.r)
    (hphase : ∀ i, g (t, d + v i) ∈ Metric.ball γ L.r)
    (hsinc : ∀ ij ∈ indexPairs n, (v ij.1 - v ij.2) / 2 ∈ Metric.ball 0 L.r)
    (hd : phaseTemperatureSum n g d t v / ((n : ℂ) * phaseTemperatureDerivative g (τ, d)) ∈
      Metric.ball 1 L.r) :
    ‖fullDensityLog n g L.Lb L.Lh L.Ls L.Ld d τ t v‖ ≤
      (n : ℝ) ^ 2 * L.K * ‖t - τ‖ + L.K * (∑ i, ‖g (t, d + v i) - γ‖) +
        4 * L.K * (n : ℝ) * (displacementSquare n v + ∑ i, ‖g (t, d + v i) - γ‖) +
        L.K * ‖phaseTemperatureSum n g d t v /
          ((n : ℂ) * phaseTemperatureDerivative g (τ, d)) - 1‖ := by
  have hp (ij : Fin n × Fin n) (hij : ij ∈ indexPairs n) :
      ‖L.Ls ((v ij.1 - v ij.2) / 2) - L.Lh ((g (t, d + v ij.1) + g (t, d + v ij.2)) / 2)‖ ≤
        L.K * ((‖v ij.1‖ ^ 2 + ‖g (t, d + v ij.1) - γ‖) +
          (‖v ij.2‖ ^ 2 + ‖g (t, d + v ij.2) - γ‖)) := by
    have hs := (L.s_bound _ (hsinc ij hij)).trans
      (mul_le_mul_of_nonneg_left (norm_half_difference_sq_le _ _) L.K_pos.le)
    have hh := (L.h_bound _ (average_mem_complex_ball (hphase ij.1) (hphase ij.2))).trans
      (mul_le_mul_of_nonneg_left (norm_average_sub_le _ _ γ) L.K_pos.le)
    have htri := norm_sub_le (L.Ls ((v ij.1 - v ij.2) / 2))
      (L.Lh ((g (t, d + v ij.1) + g (t, d + v ij.2)) / 2))
    have hn := mul_nonneg L.K_pos.le
      (add_nonneg (norm_nonneg (g (t, d + v ij.1) - γ)) (norm_nonneg (g (t, d + v ij.2) - γ)))
    nlinarith
  have hn := completeNumeratorLog_norm_le L.K_pos.le (fun i => norm_nonneg (g (t, d + v i) - γ))
    (L.b_lip t ht τ hτ) (fun i => L.h_bound _ (hphase i)) hp
  have hden := L.d_bound _ hd
  exact (norm_sub_le _ _).trans (add_le_add hn hden)

end
end IsingBulk.AnisoF002.NegativeHT
