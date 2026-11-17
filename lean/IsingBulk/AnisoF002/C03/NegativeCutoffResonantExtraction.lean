import IsingBulk.AnisoF002.C03.NegativeResonantExtraction
import IsingBulk.AnisoF002.C03.NegativeCutoffRestriction

/-!
# Exact resonant extraction below any prescribed positive cutoff

All complete physical integrals and Gaussian estimates are reconstructed
on a fixed cutoff chosen below the supplied positive bound, before N.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology Classical

set_option maxHeartbeats 1000000 in
theorem exists_actual_resonant_cycle_extraction_below_cutoff {b B : ℂ → ℂ} {φ epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ r s Mi ki a M kappa : ℝ, ∃ hs : 0 < s,
      0 < r ∧ s ≤ epsilon ∧ 0 < Mi ∧ 0 < ki ∧ 0 < a ∧ 0 < M ∧ 0 < kappa ∧
      ∀ n : ℕ, Odd (n + 1) → ∃ d : InnerRemainderFamily b B φ (n + 1) r s Mi ki,
        AnalyticOnNhd ℂ (extractedCycleRemainder d hs.le)
          (Metric.ball 0 (a / (n + 1 : ℕ))) ∧
        (∀ j : ℕ, ‖iteratedDeriv j (extractedCycleRemainder d hs.le) 0 /
            (j.factorial : ℂ)‖ ≤
          M * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) / (a / (n + 1 : ℕ)) ^ j) ∧
        (Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1 →
          (negativePhysicalCoefficient b B φ n =ᶠ[𝓝 0]
            fun t => innerCyclePoleIntegral d t + extractedCycleRemainder d hs.le t) ∧
          ∀ j : ℕ,
            IntegrableOn (fun q : Fin n → ℝ =>
              if angularShortSquare (negativeConstrainedAngles q) ≤ s then
                d.actualResidue (negativeConstrainedAngles q) /
                  d.pole (negativeConstrainedAngles q) ^ (j + 1) else 0) (regularAngularBox n) ∧
            iteratedDeriv j (negativePhysicalCoefficient b B φ n) 0 / (j.factorial : ℂ) =
              innerCyclePoleCoefficient d j +
                iteratedDeriv j (extractedCycleRemainder d hs.le) 0 / (j.factorial : ℂ)) := by
  obtain ⟨r, s, Mi, ki, hr, hs, hsε, hMi, hki, hd⟩ :=
    exists_actual_inner_remainder_families_below_cutoff hepsilon hb hB hφ hπ hBi hbsq
  obtain ⟨ro, Mo, ko, hro, hMo, hko, hout⟩ :=
    exists_actual_outer_cycle_remainders hb hB hφ hπ hBi hbsq hs
  let a := min (r / 64) (ro / 16)
  let kappa := min ki ko
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hk : 0 < kappa := lt_min hki hko
  have hai : a ≤ r / 64 := min_le_left _ _
  have hao : a ≤ ro / 16 := min_le_right _ _
  refine ⟨r, s, Mi, ki, a, Mi + Mo, kappa, hs, hr, hsε, hMi, hki, ha, add_pos hMi hMo, hk, ?_⟩
  intro n hn
  obtain ⟨d⟩ := hd (n + 1) (Nat.succ_pos n)
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨hIa, _, hIj⟩ := innerCycleRemainder_analytic_and_bound d hr hs.le hMi.le
  obtain ⟨hOa, _, hOj⟩ := hout n
  have hI0 := hIa 0 (Metric.mem_ball_self (by positivity))
  have hO0 := hOa 0 (Metric.mem_ball_self (by positivity))
  refine ⟨d, ?_, ?_, ?_⟩
  · apply (hIa.mono (Metric.ball_subset_ball ?_)).add (hOa.mono (Metric.ball_subset_ball ?_))
    · rw [show r / (16 * (n + 1 : ℕ)) = (r / 16) / (n + 1 : ℕ) by ring]
      exact div_le_div_of_nonneg_right (hai.trans (by linarith)) hN.le
    · rw [show ro / (4 * (n + 1 : ℕ)) = (ro / 4) / (n + 1 : ℕ) by ring]
      exact div_le_div_of_nonneg_right (hao.trans (by linarith)) hN.le
  · intro j
    unfold extractedCycleRemainder
    rw [iteratedDeriv_add hI0.contDiffAt hO0.contDiffAt, add_div]
    have hi : ‖iteratedDeriv j (innerCycleRemainder d hs.le) 0 / (j.factorial : ℂ)‖ ≤
        Mi * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) / (a / (n + 1 : ℕ)) ^ j := (hIj j).trans (by
      rw [show r / (64 * (n + 1 : ℕ)) = (r / 64) / (n + 1 : ℕ) by ring]
      exact gaussian_cauchy_radius_mono j hMi.le ha hN hai (min_le_left _ _))
    have ho : ‖iteratedDeriv j (outerCycleRemainder b B φ s n) 0 / (j.factorial : ℂ)‖ ≤
        Mo * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) / (a / (n + 1 : ℕ)) ^ j := (hOj j).trans (by
      rw [show ro / (16 * (n + 1 : ℕ)) = (ro / 16) / (n + 1 : ℕ) by ring]
      exact gaussian_cauchy_radius_mono j hMo.le ha hN hao (min_le_right _ _))
    calc
      _ ≤ ‖iteratedDeriv j (innerCycleRemainder d hs.le) 0 / (j.factorial : ℂ)‖ +
          ‖iteratedDeriv j (outerCycleRemainder b B φ s n) 0 / (j.factorial : ℂ)‖ := norm_add_le _ _
      _ ≤ Mi * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) / (a / (n + 1 : ℕ)) ^ j +
          Mo * Real.exp (-kappa * ((n + 1 : ℕ) : ℝ) ^ 2) / (a / (n + 1 : ℕ)) ^ j := add_le_add hi ho
      _ = _ := by ring
  · exact actual_resonant_coefficient_jets hb hB hφ hπ hBi hbsq d hr hs hMi.le hn


end
end IsingBulk.AnisoF002.NegativeHT
