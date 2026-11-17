import IsingBulk.AnisoF002.C03.NegativeGlobalGaussian

/-!
# Common analytic and Gaussian control with the exact physical normalization

The complete numerator is the actual b-dependent finite product.  Its
normalization W_n is retained in the bound so that the later real torus
integration cancels the angular volume with no lost factorial or 2π.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology

theorem exists_actual_numerator_gaussian_control {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ r M kappa : ℝ, 0 < r ∧ 0 < M ∧ 0 < kappa ∧
      ∀ n : ℕ, ∀ q : Fin n → ℝ, ∀ t ∈ Metric.closedBall (0 : ℂ) r,
        AnalyticAt ℂ
          (fun u => completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 u (fun i => (q i : ℂ))) t ∧
        ‖completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 t (fun i => (q i : ℂ))‖ ≤
          M * Real.exp (-kappa * (n : ℝ) ^ 2) / ‖windingNormalization n‖ := by
  obtain ⟨d⟩ := (exists_negative_global_controls hB hφ hπ hBi).1
  obtain ⟨M, kappa, hM, hk, hmatched⟩ := exists_matched_gaussian
    (mul_nonneg d.prefactorBound_pos.le d.bodyBound_pos.le)
    d.pairBound_pos.le d.rho_pos d.rho_lt_one
  obtain ⟨ζ, _, hζ, he⟩ := eventually_negative_complete_numerator_all_indices φ hb hB hBi hbsq
  obtain ⟨s, hs, hse⟩ := Metric.eventually_nhds_iff.mp he
  let r := min (s / 2) (d.radius / 2)
  have hr : 0 < r := lt_min (half_pos hs) (half_pos d.radius_pos)
  refine ⟨r, M, kappa, hr, hM, hk, ?_⟩
  intro n q t ht
  have hts : t ∈ Metric.ball (0 : ℂ) s :=
    (Metric.mem_closedBall.mp ht).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hs))
  have htd : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2) :=
    Metric.closedBall_subset_closedBall (min_le_right _ _) ht
  have heq : (fun u => completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 u
      (fun i => (q i : ℂ))) =ᶠ[𝓝 t]
      (fun u => (ζ ^ (n ^ 2) / windingNormalization n) *
        edgeFullNumerator (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) u q) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hts] with u hu
    exact hse hu n q
  constructor
  · exact (analyticAt_const.mul (d.fullNumerator_analytic q
      (Metric.closedBall_subset_closedBall (half_le_self d.radius_pos.le) htd))).congr heq.symm
  · rw [heq.eq_of_nhds, norm_mul, norm_div, norm_pow, hζ, one_pow]
    have hnum : ‖edgeFullNumerator (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) t q‖ ≤
        M * Real.exp (-kappa * (n : ℝ) ^ 2) := by
      simpa only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero,
        div_one] using d.fullNumerator_gaussian hmatched q htd 0
    calc
      _ ≤ (1 / ‖windingNormalization n‖) * (M * Real.exp (-kappa * (n : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = _ := by ring

end
end IsingBulk.AnisoF002.NegativeHT
