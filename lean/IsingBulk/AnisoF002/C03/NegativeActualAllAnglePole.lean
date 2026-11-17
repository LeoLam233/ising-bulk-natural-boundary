import IsingBulk.AnisoF002.C03.NegativePoleFactor
import IsingBulk.AnisoF002.C03.NegativeGlobalPhase

/-!
# Every small-angle pole of the actual negative-edge phase

The all-angle construction is attached to the single explicit physical
phase used in the complete real-cycle coefficient.  The resulting filled
phase factor is uniformly nonzero on one fixed temperature disk for every
particle population and every inner winding chart.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem exists_actual_all_angle_phase_factors {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0) :
    let g := negativeGlobalPhase B φ
    let a := fderiv ℂ g (0, 0) (1, 0)
    ∃ R σ C : ℝ, 0 < R ∧ 0 < σ ∧ 0 < C ∧ a ≠ 0 ∧
      ∀ n : ℕ, 0 < n → ∃ T : (Fin n → ℂ) → ℂ,
        AnalyticOnNhd ℂ T (Metric.ball 0 σ) ∧ T 0 = 0 ∧
        ∀ δ ∈ Metric.ball 0 σ,
          let F := centeredPhaseAverage n g ((φ : ℂ) * Complex.I) 0 δ
          F (T δ) = 0 ∧ ‖T δ‖ ≤ R / 2 ∧
          ‖T δ‖ ≤ C * displacementSquare n δ / (n : ℝ) ∧
          AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) R) ∧
          AnalyticOnNhd ℂ (dslope F (T δ)) (Metric.ball (0 : ℂ) R) ∧
          ∀ t ∈ Metric.closedBall (0 : ℂ) R,
            (∑ i, g (t, δ i)) =
              (n : ℂ) * ((φ : ℂ) * Complex.I) + (n : ℂ) * (t - T δ) * dslope F (T δ) t ∧
            ‖dslope F (T δ) t - a‖ ≤ ‖a‖ / 2 ∧
            ‖a‖ / 2 ≤ ‖dslope F (T δ) t‖ ∧
            ‖dslope F (T δ) t‖ ≤ 3 * ‖a‖ / 2 ∧ dslope F (T δ) t ≠ 0 := by
  let g := negativeGlobalPhase B φ
  let a := fderiv ℂ g (0, 0) (1, 0)
  have hg := negativeGlobalPhase_analyticAt_zero hB hφ hπ
  have hg0 : g (0, 0) = (φ : ℂ) * Complex.I := by
    simpa only [Complex.cos_zero, sub_self] using negativeGlobalPhase_center B hφ hπ 0
  have hg0' : negativeGlobalPhase B φ (0, 0) = (φ : ℂ) * Complex.I := hg0
  have hB0 : B 0 ≠ 0 := by intro hz; simp [hz] at hBi
  have hc := physical_negative_phase_temperature_derivative_ne_zero
    (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ hπ)) hB hB0 hg hg0
    (Filter.Eventually.of_forall (negativeGlobalPhase_cosh B φ))
  obtain ⟨r, σ, C, hr, hσ, hC, _, _, hconstruct⟩ :=
    exists_uniform_analytic_all_angle_poles hg hc (negativeGlobalPhase_even B φ)
  refine ⟨r / 4, σ, C, by positivity, hσ, hC, hc, ?_⟩
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨T, hTa, hT0, hT⟩ := hconstruct n hn
  refine ⟨T, hTa, hT0, ?_⟩
  intro δ hδ
  let F := centeredPhaseAverage n g ((φ : ℂ) * Complex.I) 0 δ
  obtain ⟨hlevel, hnorm, hquad, _, hlocal, _⟩ := hT δ hδ
  have hzero : F (T δ) = 0 := by
    apply (centeredPhaseAverage_eq_zero_iff hn g ((φ : ℂ) * Complex.I) 0 δ (T δ)).mpr
    simpa only [zero_add, g, hg0'] using hlevel
  have hFa : AnalyticOnNhd ℂ F (Metric.closedBall (0 : ℂ) (r / 4)) := by
    intro t ht
    simpa only [F, g, hg0'] using (hlocal t ht).1
  have hclose (t : ℂ) (ht : t ∈ Metric.closedBall (0 : ℂ) (r / 4)) :
      ‖deriv F t - a‖ ≤ ‖a‖ / 2 := by
    simpa only [F, a, g, hg0'] using (hlocal t ht).2
  have hTin : T δ ∈ Metric.ball (0 : ℂ) (r / 4) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  obtain ⟨hAa, hA⟩ := phase_factor_uniform hc hFa hclose hTin hzero
  refine ⟨hzero, by linarith, hquad, hFa, hAa, ?_⟩
  intro t ht
  obtain ⟨he, hcl, hlo, hup, hne⟩ := hA t ht
  refine ⟨?_, hcl, hlo, hup, hne⟩
  have hsum : (∑ i, g (t, δ i)) = (n : ℂ) * ((φ : ℂ) * Complex.I) + (n : ℂ) * F t := by
    dsimp [F, centeredPhaseAverage]
    simp only [zero_add, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  rw [hsum, he]
  ring

end
end IsingBulk.AnisoF002.NegativeHT
