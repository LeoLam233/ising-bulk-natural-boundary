import IsingBulk.AnisoF002.C03.NegativeCycleDecomposition

/-!
# All-winding extraction of the genuine resonant Taylor coefficient

The original complete coefficient is decomposed on a genuine physical
disk.  Its residue term retains every inner winding.  The other two terms
are actual analytic integrals and have a common Gaussian Cauchy bound on
a c/N disk.  All constants are chosen before the particle number.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology Classical

def extractedCycleRemainder {b B : ℂ → ℂ} {φ r s M kappa : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa) (hs : 0 ≤ s) : ℂ → ℂ :=
  innerCycleRemainder d hs + outerCycleRemainder b B φ s n

set_option maxHeartbeats 1000000 in
theorem actual_resonant_coefficient_jets {b B : ℂ → ℂ} {φ r s M kappa : ℝ} {n : ℕ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t)
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa)
    (hr : 0 < r) (hs : 0 < s) (hM : 0 ≤ M) (hn : Odd (n + 1))
    (hres : Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1) :
    (negativePhysicalCoefficient b B φ n =ᶠ[𝓝 0]
      fun t => innerCyclePoleIntegral d t + extractedCycleRemainder d hs.le t) ∧
    ∀ j : ℕ,
      IntegrableOn (fun q : Fin n → ℝ =>
        if angularShortSquare (negativeConstrainedAngles q) ≤ s then
          d.actualResidue (negativeConstrainedAngles q) /
            d.pole (negativeConstrainedAngles q) ^ (j + 1) else 0) (regularAngularBox n) ∧
      iteratedDeriv j (negativePhysicalCoefficient b B φ n) 0 / (j.factorial : ℂ) =
        innerCyclePoleCoefficient d j +
          iteratedDeriv j (extractedCycleRemainder d hs.le) 0 / (j.factorial : ℂ) := by
  obtain ⟨c, Mp, kp, Ap, hc, hMp, _, hAp, hphys⟩ :=
    exists_actual_physical_cycle_control hb hB hφ hπ hBi hbsq
  obtain ⟨rμ, hrμ, hμ⟩ := exists_actual_real_density_measurable hb hB hφ hπ hBi hbsq
  obtain ⟨ro, Mo, ko, hro, _, _, hout⟩ :=
    exists_actual_outer_cycle_remainders hb hB hφ hπ hBi hbsq hs
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  let cn : ℝ := c / ((n + 1 : ℕ) : ℝ) ^ 2
  let E : ℝ := Mp * ((n + 1 : ℕ) : ℝ) * Real.exp (-kp * ((n + 1 : ℕ) : ℝ) ^ 2) /
    ‖windingNormalization (n + 1)‖
  let delta : ℝ := min (r / (4 * (n + 1 : ℕ))) (min (cn / 2) rμ)
  have hcn : 0 < cn := by dsimp [cn]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hdelta : 0 < delta := lt_min (by positivity) (lt_min (half_pos hcn) hrμ)
  have hdeltaR : delta ≤ r / (4 * (n + 1 : ℕ)) := min_le_left _ _
  have hdeltaC : delta ≤ cn / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaμ : delta ≤ rμ := (min_le_right _ _).trans (min_le_right _ _)
  have hmeas (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) delta) :
      Measurable (realNegativeDensity b B φ (n + 1) t) :=
    hμ (n + 1) (Nat.succ_pos n) t (Metric.ball_subset_ball hdeltaμ ht)
  have hbound (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) delta) (q : Fin n → ℝ) :
      ‖realNegativeDensity b B φ (n + 1) t (negativeConstrainedAngles q)‖ ≤ E :=
    (hphys n hn q t (Metric.ball_subset_closedBall
      (Metric.ball_subset_ball (hdeltaC.trans (half_le_self hcn.le)) ht))).2.2
  have hsep (q : Fin n → ℝ) (hq : angularShortSquare (negativeConstrainedAngles q) ≤ s) :
      cn ≤ ‖d.pole (negativeConstrainedAngles q)‖ :=
    (extracted_pole_outside_physical_disk d hc hAp q hq
      (fun t ht => (hphys n hn q t ht).2.1)).le
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) delta := Metric.mem_ball_self hdelta
  obtain ⟨hPa, hPj⟩ := innerCyclePoleIntegral_normalized_jets d hr hs.le hM hcn hE hres
    (hmeas 0 hzero) (hbound 0 hzero) hsep
  have hIa := (innerCycleRemainder_analytic_and_bound d hr hs.le hM).1
  have hOa := (hout n).1
  have hI0 := hIa 0 (Metric.mem_ball_self (by positivity))
  have hO0 := hOa 0 (Metric.mem_ball_self (by positivity))
  have heq : negativePhysicalCoefficient b B φ n =ᶠ[𝓝 0]
      (fun t => innerCyclePoleIntegral d t + innerCycleRemainder d hs.le t +
        outerCycleRemainder b B φ s n t) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hdelta] with t ht
    exact actual_coefficient_inner_outer_decomposition d hr hs.le hM hcn hE
      hdelta hdeltaR hdeltaC hres hmeas hbound hsep t ht
  constructor
  · filter_upwards [heq] with t ht
    simpa only [extractedCycleRemainder, Pi.add_apply, add_assoc] using ht
  · intro j
    refine ⟨(hPj j).1, ?_⟩
    rw [normalized_jets_of_three_analytic_germs heq
      (hPa 0 (Metric.mem_ball_self (half_pos hcn))) hI0 hO0 j, (hPj j).2]
    unfold extractedCycleRemainder
    rw [iteratedDeriv_add hI0.contDiffAt hO0.contDiffAt]
    ring

theorem gaussian_cauchy_radius_mono {M kappa kappa0 r a N : ℝ} (j : ℕ)
    (hM : 0 ≤ M) (ha : 0 < a) (hN : 0 < N) (har : a ≤ r) (hk : kappa0 ≤ kappa) :
    M * Real.exp (-kappa * N ^ 2) / (r / N) ^ j ≤
      M * Real.exp (-kappa0 * N ^ 2) / (a / N) ^ j := by
  apply div_le_div₀ (by positivity)
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg N])) hM)
    (pow_pos (div_pos ha hN) j)
    (pow_le_pow_left₀ (div_pos ha hN).le (div_le_div_of_nonneg_right har hN.le) j)

set_option maxHeartbeats 1000000 in
theorem exists_actual_resonant_cycle_extraction {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ r s Mi ki a M kappa : ℝ, ∃ hs : 0 < s,
      0 < r ∧ 0 < Mi ∧ 0 < ki ∧ 0 < a ∧ 0 < M ∧ 0 < kappa ∧
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
  obtain ⟨r, s, Mi, ki, hr, hs, hMi, hki, hd⟩ :=
    exists_actual_inner_remainder_families hb hB hφ hπ hBi hbsq
  obtain ⟨ro, Mo, ko, hro, hMo, hko, hout⟩ :=
    exists_actual_outer_cycle_remainders hb hB hφ hπ hBi hbsq hs
  let a := min (r / 64) (ro / 16)
  let kappa := min ki ko
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hk : 0 < kappa := lt_min hki hko
  have hai : a ≤ r / 64 := min_le_left _ _
  have hao : a ≤ ro / 16 := min_le_right _ _
  refine ⟨r, s, Mi, ki, a, Mi + Mo, kappa, hs, hr, hMi, hki, ha, add_pos hMi hMo, hk, ?_⟩
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
