import IsingBulk.AnisoF002.C03.NegativeGlobalNumerator

/-!
# All parameter jets of the actual complete negative-edge numerator

The common disk is chosen before the particle number and derivative order.
The physical square-root phase and the exact finite normalization are
retained in the analytic identity used to transfer the matched estimate.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem windingNormalization_norm_ge_one (n : ℕ) : 1 ≤ ‖windingNormalization n‖ := by
  unfold windingNormalization
  rw [norm_mul, norm_pow]
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hp : (1 : ℝ) ≤ ‖(2 : ℂ) * (Real.pi : ℂ)‖ := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hpi : 1 ≤ Real.pi := by
      have hh := Real.sin_le (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
      rw [Real.sin_pi_div_two] at hh
      linarith
    linarith
  have hpow : 1 ≤ ‖(2 : ℂ) * (Real.pi : ℂ)‖ ^ (n - 1) := one_le_pow₀ hp
  simpa only [Complex.norm_natCast] using one_le_mul_of_one_le_of_one_le hf hpow

set_option maxHeartbeats 1000000 in
theorem exists_negative_global_numerator_jets {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ r kappa C : ℝ, 0 < r ∧ 0 < kappa ∧ 0 < C ∧
      ∀ j : ℕ, ∃ Cj : ℝ, 0 < Cj ∧
        ∀ n : ℕ, 0 < n → ∀ x : Fin n → ℝ,
          ∀ t ∈ Metric.closedBall (0 : ℂ) r,
            ‖iteratedDeriv j
              (fun u => completeNegativeNumerator n b (negativeGlobalPhase B φ)
                0 u (fun i => (x i : ℂ))) t‖ ≤
              Cj * Real.exp (-kappa * (n : ℝ) ^ 2 +
                C * (n : ℝ) * Real.log ((n : ℝ) + 1)) := by
  obtain ⟨d⟩ := (exists_negative_global_controls hB hφ hπ hBi).1
  obtain ⟨ζ, _, hζ, he⟩ := eventually_negative_complete_numerator_all_indices φ hb hB hBi hbsq
  obtain ⟨s, hs, hse⟩ := Metric.eventually_nhds_iff.mp he
  let r := min (s / 2) (d.radius / 2)
  have hr : 0 < r := lt_min (half_pos hs) (half_pos d.radius_pos)
  obtain ⟨kappa, C, hk, hC, hjet⟩ := d.matched_pfaffian_numerator_estimate
  refine ⟨r, kappa, C, hr, hk, hC, ?_⟩
  intro j
  obtain ⟨Cj, hCj, hj⟩ := hjet j
  refine ⟨Cj, hCj, ?_⟩
  intro n hn x t ht
  have hts : t ∈ Metric.ball (0 : ℂ) s := by
    have htn : dist t 0 ≤ r := ht
    exact (htn.trans (min_le_left _ _)).trans_lt (half_lt_self hs)
  have heq : (fun u => completeNegativeNumerator n b (negativeGlobalPhase B φ)
      0 u (fun i => (x i : ℂ))) =ᶠ[𝓝 t]
      (fun u => (ζ ^ (n ^ 2) / windingNormalization n) *
        edgeFullNumerator (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) u x) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hts] with u hu
    exact hse hu n x
  have htd : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2) :=
    Metric.closedBall_subset_closedBall (min_le_right _ _) ht
  rw [heq.iteratedDeriv_eq j, iteratedDeriv_const_mul_field, norm_mul]
  have hnorm : ‖ζ ^ (n ^ 2) / windingNormalization n‖ ≤ 1 := by
    rw [norm_div, norm_pow, hζ, one_pow]
    exact (div_le_one (lt_of_lt_of_le zero_lt_one (windingNormalization_norm_ge_one n))).mpr
      (windingNormalization_norm_ge_one n)
  exact (mul_le_of_le_one_left (norm_nonneg _) hnorm).trans (hj n hn x t htd)

end
end IsingBulk.AnisoF002.NegativeHT
