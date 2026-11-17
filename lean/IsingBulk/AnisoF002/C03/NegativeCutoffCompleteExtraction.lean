import IsingBulk.AnisoF002.C03.NegativeFullTaylorExtraction
import IsingBulk.AnisoF002.C03.NegativeCutoffResonantExtraction

/-!
# Complete actual Taylor extraction with an independently prescribed cutoff

The full odd-particle remainder and all-winding residue family use the
same fixed cutoff, chosen below any geometric smallness bound before N.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology Classical BigOperators

set_option maxHeartbeats 1000000 in
theorem exists_complete_actual_analytic_remainder_below_cutoff {b B : ℂ → ℂ} {φ epsilon : ℝ} {p : ℕ}
    (hepsilon : 0 < epsilon)
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t)
    (hp : 0 < p) (hperiod : Complex.exp (-((p : ℂ) * ((φ : ℂ) * Complex.I))) = 1) :
    ∃ r s Mi ki a M kappa A : ℝ, ∃ hs : 0 < s,
      0 < r ∧ s ≤ epsilon ∧ 0 < Mi ∧ 0 < ki ∧ 0 < a ∧ 0 < M ∧ 0 < kappa ∧ 0 < A ∧
      ∃ D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) r s Mi ki,
        (∀ n : ℕ, AnalyticOnNhd ℂ (completeCycleAnalyticRemainder D hs.le n)
          (Metric.ball 0 (a / (2 * n + 1 : ℕ)))) ∧
        (∀ j n : ℕ,
          physicalOddTaylorCoefficient b B φ j n = completeCyclePoleCoefficient D j n +
            iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 / (j.factorial : ℂ)) ∧
        (∀ n : ℕ, Complex.exp (-(((2 * n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1 →
          ∀ j : ℕ, IntegrableOn (fun q : Fin (2 * n) → ℝ =>
            if angularShortSquare (negativeConstrainedAngles q) ≤ s then
              (D n).actualResidue (negativeConstrainedAngles q) /
                (D n).pole (negativeConstrainedAngles q) ^ (j + 1) else 0) (regularAngularBox (2 * n))) ∧
        (∀ j n : ℕ, ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 /
            (j.factorial : ℂ)‖ ≤ M * Real.exp (-kappa * ((2 * n + 1 : ℕ) : ℝ) ^ 2) /
              (a / (2 * n + 1 : ℕ)) ^ j) ∧
        ∀ j : ℕ,
          Summable (fun n : ℕ => ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 /
            (j.factorial : ℂ)‖) ∧
          Summable (fun n : ℕ => iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 /
            (j.factorial : ℂ)) ∧
          (∑' n : ℕ, ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 /
            (j.factorial : ℂ)‖) ≤
            Real.exp ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) + A * j + A) := by
  obtain ⟨r, s, Mi, ki, ar, Mr, kr, hs, hr, hsε, hMi, hki, har, hMr, hkr, hd⟩ :=
    exists_actual_resonant_cycle_extraction_below_cutoff hepsilon hb hB hφ hπ hBi hbsq
  obtain ⟨an, Mn, kn, han, hMn, hkn, hnon⟩ :=
    exists_actual_nonresonant_coefficient_bounds hb hB hφ hπ hBi hbsq hp hperiod
  have hodd (n : ℕ) : Odd (2 * n + 1) := ⟨n, rfl⟩
  choose D hDa hDj hDe using fun n : ℕ => hd (2 * n) (hodd n)
  let a := min ar (an / 16)
  let kappa := min kr kn
  have ha : 0 < a := lt_min har (by positivity)
  have hk : 0 < kappa := lt_min hkr hkn
  have haR : a ≤ ar := min_le_left _ _
  have haN : a ≤ an / 16 := min_le_right _ _
  have hbound (j n : ℕ) :
      ‖iteratedDeriv j (completeCycleAnalyticRemainder D hs.le n) 0 / (j.factorial : ℂ)‖ ≤
        (Mr + Mn) * Real.exp (-kappa * ((2 * n + 1 : ℕ) : ℝ) ^ 2) / (a / (2 * n + 1 : ℕ)) ^ j := by
    have hN : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
    by_cases hres : Complex.exp (-(((2 * n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1
    · simp only [completeCycleAnalyticRemainder, hres, ↓reduceIte]
      apply (hDj n j).trans
      apply (gaussian_cauchy_radius_mono j hMr.le ha hN haR (min_le_left _ _)).trans
      gcongr
      linarith
    · simp only [completeCycleAnalyticRemainder, hres, ↓reduceIte]
      apply ((hnon (2 * n) hres).2.2 j).trans
      rw [show an / (16 * (2 * n + 1 : ℕ)) = (an / 16) / (2 * n + 1 : ℕ) by ring]
      apply (gaussian_cauchy_radius_mono j hMn.le ha hN haN (min_le_right _ _)).trans
      gcongr
      linarith
  obtain ⟨A, hA, hsum⟩ := complete_odd_gaussian_remainder_sum (add_pos hMr hMn) ha hk hbound
  refine ⟨r, s, Mi, ki, a, Mr + Mn, kappa, A, hs, hr, hsε, hMi, hki, ha, add_pos hMr hMn, hk, hA,
    D, ?_, ?_, ?_, hbound, hsum⟩
  · intro n
    have hN : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
    by_cases hres : Complex.exp (-(((2 * n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1
    · simp only [completeCycleAnalyticRemainder, hres, ↓reduceIte]
      exact (hDa n).mono (Metric.ball_subset_ball (div_le_div_of_nonneg_right haR hN.le))
    · simp only [completeCycleAnalyticRemainder, hres, ↓reduceIte]
      apply ((hnon (2 * n) hres).1).mono (Metric.ball_subset_ball ?_)
      rw [show an / (4 * (2 * n + 1 : ℕ)) = (an / 4) / (2 * n + 1 : ℕ) by ring]
      exact div_le_div_of_nonneg_right (haN.trans (by linarith)) hN.le
  · intro j n
    by_cases hres : Complex.exp (-(((2 * n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1
    · simpa only [completeCycleAnalyticRemainder, completeCyclePoleCoefficient, hres, ↓reduceIte,
        physicalOddTaylorCoefficient] using ((hDe n hres).2 j).2
    · simp only [completeCycleAnalyticRemainder, completeCyclePoleCoefficient, hres, ↓reduceIte,
        physicalOddTaylorCoefficient, zero_add]
  · intro n hres j
    exact ((hDe n hres).2 j).1


end
end IsingBulk.AnisoF002.NegativeHT
