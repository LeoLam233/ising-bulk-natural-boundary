import IsingBulk.AnisoF002.C03.NegativePoleExtraction

/-!
# Quantitative bounds for the filled exact pole numerator

The factor 1/n is retained before applying Cauchy's estimate on a disk of
radius R/n.  It cancels the shrinking analytic radius in the remainder
bound, giving the same complete Gaussian numerator scale for every n.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology

theorem filledPoleNumerator_analytic {H F : ℂ → ℂ} {n : ℕ} {T : ℂ} {R : ℝ}
    (hn : 0 < n) (hH : AnalyticOnNhd ℂ H (Metric.ball (0 : ℂ) R))
    (hF : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) R))
    (hT : T ∈ Metric.ball (0 : ℂ) R)
    (hA : ∀ t ∈ Metric.ball (0 : ℂ) R, dslope F T t ≠ 0)
    (he : ∀ t ∈ Metric.ball (0 : ℂ) R,
      dslope Complex.exp 0 (-((n : ℂ) * F t)) ≠ 0) :
    AnalyticOnNhd ℂ (filledPoleNumerator H F n T) (Metric.ball (0 : ℂ) R) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hAa := analyticOnNhd_dslope_ball hF hT
  intro t ht
  have harg : AnalyticAt ℂ (fun u => -((n : ℂ) * F u)) t :=
    (analyticAt_const.mul (hF t ht)).neg
  have hea := (exponential_dslope_entire _ (mem_univ _)).comp harg
  exact ((hH t ht).mul (analyticAt_const.add harg.cexp)).div
    ((analyticAt_const.mul (hAa t ht)).mul hea)
    (mul_ne_zero (mul_ne_zero hn0 (hA t ht)) (he t ht))

theorem filledPoleNumerator_norm_le {H F : ℂ → ℂ} {n : ℕ} {T t : ℂ} {A E : ℝ}
    (hn : 0 < n) (hA : 0 < A) (hE : 0 ≤ E) (hH : ‖H t‖ ≤ E)
    (hfactor : A / 2 ≤ ‖dslope F T t‖)
    (hexp : ‖Complex.exp (-((n : ℂ) * F t))‖ ≤ 2)
    (he : 1 / 2 ≤ ‖dslope Complex.exp 0 (-((n : ℂ) * F t))‖) :
    ‖filledPoleNumerator H F n T t‖ ≤ 12 * E / ((n : ℝ) * A) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnum : ‖H t‖ * ‖1 + Complex.exp (-((n : ℂ) * F t))‖ ≤ 3 * E := by
    have hb : ‖1 + Complex.exp (-((n : ℂ) * F t))‖ ≤ 3 := by
      have hh := norm_add_le (1 : ℂ) (Complex.exp (-((n : ℂ) * F t)))
      rw [norm_one] at hh
      linarith
    calc
      _ ≤ E * 3 := mul_le_mul hH hb (norm_nonneg _) hE
      _ = _ := by ring
  have hden : (n : ℝ) * A / 4 ≤
      (n : ℝ) * ‖dslope F T t‖ * ‖dslope Complex.exp 0 (-((n : ℂ) * F t))‖ := by
    calc
      _ = (n : ℝ) * (A / 2) * (1 / 2) := by ring
      _ ≤ _ := by gcongr
  have hdpos : 0 < (n : ℝ) * ‖dslope F T t‖ *
      ‖dslope Complex.exp 0 (-((n : ℂ) * F t))‖ :=
    (show 0 < (n : ℝ) * A / 4 by positivity).trans_le hden
  unfold filledPoleNumerator
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_natCast]
  apply (div_le_iff₀ hdpos).mpr
  calc
    _ ≤ 3 * E := hnum
    _ = 12 * E / ((n : ℝ) * A) * ((n : ℝ) * A / 4) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

theorem filledPoleNumerator_remainder_bound {H F : ℂ → ℂ} {n : ℕ} {T : ℂ}
    {R A E : ℝ} (hn : 0 < n) (hR : 0 < R) (hA : 0 < A) (hE : 0 ≤ E)
    (hH : AnalyticOnNhd ℂ H (Metric.ball (0 : ℂ) (R / (n : ℝ))))
    (hF : AnalyticOnNhd ℂ F (Metric.ball (0 : ℂ) (R / (n : ℝ))))
    (hT : ‖T‖ ≤ R / (4 * (n : ℝ)))
    (hcontrol : ∀ t ∈ Metric.ball (0 : ℂ) (R / (n : ℝ)),
      ‖H t‖ ≤ E ∧ A / 2 ≤ ‖dslope F T t‖ ∧
        ‖Complex.exp (-((n : ℂ) * F t))‖ ≤ 2 ∧
        1 / 2 ≤ ‖dslope Complex.exp 0 (-((n : ℂ) * F t))‖) :
    AnalyticOnNhd ℂ (dslope (filledPoleNumerator H F n T) T)
      (Metric.ball (0 : ℂ) (R / (n : ℝ))) ∧
      ∀ t ∈ Metric.ball (0 : ℂ) (R / (4 * (n : ℝ))),
        ‖dslope (filledPoleNumerator H F n T) T t‖ ≤ 48 * E / (A * R) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrad : 0 < R / (n : ℝ) := div_pos hR hnR
  have hT' : ‖T‖ ≤ (R / (n : ℝ)) / 4 := by
    convert hT using 1
    ring
  have hTin : T ∈ Metric.ball (0 : ℂ) (R / (n : ℝ)) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hKa := filledPoleNumerator_analytic hn hH hF hTin
    (fun t ht => norm_pos_iff.mp ((half_pos hA).trans_le (hcontrol t ht).2.1))
    (fun t ht => norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (hcontrol t ht).2.2.2))
  obtain ⟨hRa, hRb⟩ := analytic_remainder_uniform_bound hrad hKa
    (fun t ht => filledPoleNumerator_norm_le hn hA hE (hcontrol t ht).1
      (hcontrol t ht).2.1 (hcontrol t ht).2.2.1 (hcontrol t ht).2.2.2) hT'
  refine ⟨hRa, ?_⟩
  intro t ht
  have ht' : t ∈ Metric.ball (0 : ℂ) ((R / (n : ℝ)) / 4) := by
    convert ht using 1
    ring
  calc
    _ ≤ 4 * (12 * E / ((n : ℝ) * A)) / (R / (n : ℝ)) := hRb t ht'
    _ = _ := by field_simp; ring

end
end IsingBulk.AnisoF002.NegativeHT
