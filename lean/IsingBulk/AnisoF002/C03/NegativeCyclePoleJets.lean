import IsingBulk.AnisoF002.C03.NegativeCyclePoleRepresentation

/-!
# Exact all-order coefficients of the actual inner residue integral

The minus sign, full numerator, full phase derivative, and literal
independent angular measure are all retained.  Pole separation and
measurability are proved from the complete physical cycle.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology Classical

set_option maxHeartbeats 1000000 in
theorem innerCyclePoleIntegral_normalized_jets {b B : ℂ → ℂ} {φ r s M kappa c E : ℝ} {n : ℕ}
    (d : InnerRemainderFamily b B φ (n + 1) r s M kappa)
    (hr : 0 < r) (hs : 0 ≤ s) (hM : 0 ≤ M) (hc : 0 < c) (hE : 0 ≤ E)
    (hres : Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1)
    (hmeas : Measurable (realNegativeDensity b B φ (n + 1) 0))
    (hbound : ∀ q : Fin n → ℝ, ‖realNegativeDensity b B φ (n + 1) 0 (negativeConstrainedAngles q)‖ ≤ E)
    (hsep : ∀ q : Fin n → ℝ, angularShortSquare (negativeConstrainedAngles q) ≤ s →
      c ≤ ‖d.pole (negativeConstrainedAngles q)‖) :
    AnalyticOnNhd ℂ (innerCyclePoleIntegral d) (Metric.ball 0 (c / 2)) ∧
      ∀ j : ℕ,
        IntegrableOn (fun q : Fin n → ℝ =>
          if angularShortSquare (negativeConstrainedAngles q) ≤ s then
            d.actualResidue (negativeConstrainedAngles q) /
              d.pole (negativeConstrainedAngles q) ^ (j + 1) else 0) (regularAngularBox n) ∧
        iteratedDeriv j (innerCyclePoleIntegral d) 0 / (j.factorial : ℂ) = innerCyclePoleCoefficient d j := by
  obtain ⟨A, P, L, hL, hAm, hPm, hAb, hPb, hsame, hzero⟩ :=
    exists_inner_cycle_pole_representatives d hr hs hM hc hE hres hmeas hbound hsep
  let μ : Measure (Fin n → ℝ) := volume.restrict (regularAngularBox n)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    rw [regularAngularBox_volume]
    exact ENNReal.ofReal_ne_top)
  have hkernel (t : ℂ) (q : Fin n → ℝ) : A q / (t - P q) =
      if angularShortSquare (negativeConstrainedAngles q) ≤ s then
        d.actualResidue (negativeConstrainedAngles q) / (t - d.pole (negativeConstrainedAngles q)) else 0 := by
    by_cases hq : angularShortSquare (negativeConstrainedAngles q) ≤ s
    · simp only [hq, ↓reduceIte, (hsame q hq).1, (hsame q hq).2]
    · simp only [hq, ↓reduceIte, hzero q hq, zero_div]
  have hIeq : (fun t : ℂ => ∫ q, A q / (t - P q) ∂μ) = innerCyclePoleIntegral d := by
    funext t
    exact integral_congr_ae (Eventually.of_forall (hkernel t))
  constructor
  · rw [← hIeq]
    apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
    intro t ht
    have hd := (integral_pole_power_hasDerivAt (μ := μ) hc hAm hPm hAb hPb 0 ht).2
    simpa only [Nat.zero_add, pow_one] using hd.differentiableAt.differentiableWithinAt
  · intro j
    have hjkernel (q : Fin n → ℝ) : A q / P q ^ (j + 1) =
        if angularShortSquare (negativeConstrainedAngles q) ≤ s then
          d.actualResidue (negativeConstrainedAngles q) / d.pole (negativeConstrainedAngles q) ^ (j + 1) else 0 := by
      by_cases hq : angularShortSquare (negativeConstrainedAngles q) ≤ s
      · simp only [hq, ↓reduceIte, (hsame q hq).1, (hsame q hq).2]
      · simp only [hq, ↓reduceIte, hzero q hq, zero_div]
    have hi : Integrable (fun q => A q / P q ^ (j + 1)) μ := by
      apply (integrable_const (L / c ^ (j + 1))).mono'
        ((hAm.div (hPm.pow_const _)).aestronglyMeasurable)
      apply Eventually.of_forall
      intro q
      change ‖A q / P q ^ (j + 1)‖ ≤ L / c ^ (j + 1)
      rw [norm_div, norm_pow]
      exact div_le_div₀ hL.le (hAb q) (pow_pos hc _) (pow_le_pow_left₀ hc.le (hPb q) _)
    refine ⟨hi.congr (Eventually.of_forall hjkernel), ?_⟩
    rw [← hIeq, normalized_pole_integral_coefficient (μ := μ) hc hAm hPm hAb hPb]
    congr 1
    exact integral_congr_ae (Eventually.of_forall hjkernel)

theorem exists_actual_inner_cycle_pole_jets {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ r s M kappa c : ℝ, 0 < r ∧ 0 < s ∧ 0 < M ∧ 0 < kappa ∧ 0 < c ∧
      ∀ n : ℕ, Odd (n + 1) →
      ∃ d : InnerRemainderFamily b B φ (n + 1) r s M kappa,
        Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1 →
          AnalyticOnNhd ℂ (innerCyclePoleIntegral d)
            (Metric.ball 0 ((c / ((n + 1 : ℕ) : ℝ) ^ 2) / 2)) ∧
          ∀ j : ℕ,
            IntegrableOn (fun q : Fin n → ℝ =>
              if angularShortSquare (negativeConstrainedAngles q) ≤ s then
                d.actualResidue (negativeConstrainedAngles q) /
                  d.pole (negativeConstrainedAngles q) ^ (j + 1) else 0) (regularAngularBox n) ∧
            iteratedDeriv j (innerCyclePoleIntegral d) 0 / (j.factorial : ℂ) = innerCyclePoleCoefficient d j := by
  obtain ⟨r, s, M, kappa, hr, hs, hM, hk, hd⟩ := exists_actual_inner_remainder_families hb hB hφ hπ hBi hbsq
  obtain ⟨c, Mp, kp, Ap, hc, hMp, hkp, hAp, hphys⟩ := exists_actual_physical_cycle_control hb hB hφ hπ hBi hbsq
  obtain ⟨rμ, hrμ, hμ⟩ := exists_actual_real_density_measurable hb hB hφ hπ hBi hbsq
  refine ⟨r, s, M, kappa, c, hr, hs, hM, hk, hc, ?_⟩
  intro n hn
  obtain ⟨d⟩ := hd (n + 1) (Nat.succ_pos n)
  refine ⟨d, ?_⟩
  intro hres
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcn : 0 < c / ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
  apply innerCyclePoleIntegral_normalized_jets d hr hs.le hM.le hcn
    (E := Mp * ((n + 1 : ℕ) : ℝ) * Real.exp (-kp * ((n + 1 : ℕ) : ℝ) ^ 2) /
      ‖windingNormalization (n + 1)‖) (by positivity) hres
  · exact hμ (n + 1) (Nat.succ_pos n) 0 (Metric.mem_ball_self hrμ)
  · intro q
    exact (hphys n hn q 0 (Metric.mem_closedBall_self hcn.le)).2.2
  · intro q hq
    exact (extracted_pole_outside_physical_disk d hc hAp q hq
      (fun t ht => (hphys n hn q t ht).2.1)).le

end
end IsingBulk.AnisoF002.NegativeHT
