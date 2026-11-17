import IsingBulk.AnisoF002.C03.NegativeResonantExtraction
import IsingBulk.AnisoF002.C03.NegativeNonresonantCoefficients
import IsingBulk.AnisoF002.C03.NegativeGaussianMomentSum
import IsingBulk.AnisoF002.C03.NegativeLowParticleSum

/-!
# The complete analytic remainder over every odd particle population

Resonant coefficients contribute their exact inner/outer analytic
remainders.  Every nonresonant coefficient is retained in full.  The
resulting actual remainder series is absolutely summable at every Taylor
order, with half-order logarithmic growth.  No particle or winding
competitor is discarded.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology Classical BigOperators

def completeCycleAnalyticRemainder {b B : ℂ → ℂ} {φ r s Mi ki : ℝ}
    (D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) r s Mi ki) (hs : 0 ≤ s)
    (n : ℕ) : ℂ → ℂ :=
  if Complex.exp (-(((2 * n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1 then
    extractedCycleRemainder (D n) hs else negativePhysicalCoefficient b B φ (2 * n)

def completeCyclePoleCoefficient {b B : ℂ → ℂ} {φ r s Mi ki : ℝ}
    (D : ∀ n : ℕ, InnerRemainderFamily b B φ (2 * n + 1) r s Mi ki) (j n : ℕ) : ℂ :=
  if Complex.exp (-(((2 * n + 1 : ℕ) : ℂ) * ((φ : ℂ) * Complex.I))) = 1 then
    innerCyclePoleCoefficient (D n) j else 0

theorem complete_odd_gaussian_remainder_sum {F : ℕ → ℕ → ℂ} {M a kappa : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hk : 0 < kappa)
    (hbnd : ∀ j n : ℕ, ‖F j n‖ ≤
      M * Real.exp (-kappa * ((2 * n + 1 : ℕ) : ℝ) ^ 2) /
        (a / (2 * n + 1 : ℕ)) ^ j) :
    ∃ A : ℝ, 0 < A ∧ ∀ j : ℕ,
      Summable (fun n => ‖F j n‖) ∧ Summable (F j) ∧
      (∑' n : ℕ, ‖F j n‖) ≤
        Real.exp ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) + A * j + A) := by
  obtain ⟨A0, hA0, hsum⟩ := exists_scaled_gaussian_moment_bound hk (inv_pos.mpr ha)
  let A := A0 + |Real.log M| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro n m h
    change 2 * n + 1 = 2 * m + 1 at h
    omega
  refine ⟨A, hA, ?_⟩
  intro j
  let g : ℕ → ℝ := fun N => M * ((a⁻¹ * (N : ℝ)) ^ j * Real.exp (-kappa * (N : ℝ) ^ 2))
  have hsg : Summable g := (hsum j).1.mul_left M
  have hsodd : Summable (fun n : ℕ => g (2 * n + 1)) := hsg.comp_injective hinj
  have hle (n : ℕ) : ‖F j n‖ ≤ g (2 * n + 1) := by
    apply (hbnd j n).trans_eq
    dsimp [g]
    rw [div_pow, inv_mul_eq_div, div_pow]
    field_simp
  have hsN : Summable (fun n => ‖F j n‖) := hsodd.of_norm_bounded (fun n => by
    simpa only [norm_norm] using hle n)
  refine ⟨hsN, hsN.of_norm, ?_⟩
  have hoddle : (∑' n : ℕ, g (2 * n + 1)) ≤ ∑' N : ℕ, g N :=
    hsodd.tsum_le_tsum_of_inj (fun n : ℕ => 2 * n + 1) hinj
      (fun N _ => by dsimp [g]; positivity) (fun _ => le_rfl) hsg
  calc
    _ ≤ ∑' n : ℕ, g (2 * n + 1) := hsN.tsum_le_tsum hle hsodd
    _ ≤ ∑' N : ℕ, g N := hoddle
    _ = M * ∑' N : ℕ, (a⁻¹ * (N : ℝ)) ^ j * Real.exp (-kappa * (N : ℝ) ^ 2) := tsum_mul_left
    _ ≤ M * Real.exp ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) + A0 * j + A0) :=
      mul_le_mul_of_nonneg_left (hsum j).2 hM.le
    _ = Real.exp (Real.log M + ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) + A0 * j + A0)) := by
      conv_rhs => rw [Real.exp_add, Real.exp_log hM]
    _ ≤ _ := Real.exp_le_exp.mpr (by
      dsimp [A]
      nlinarith [le_abs_self (Real.log M), abs_nonneg (Real.log M), Nat.cast_nonneg (α := ℝ) j])

set_option maxHeartbeats 1000000 in
theorem exists_complete_actual_analytic_remainder {b B : ℂ → ℂ} {φ : ℝ} {p : ℕ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t)
    (hp : 0 < p) (hperiod : Complex.exp (-((p : ℂ) * ((φ : ℂ) * Complex.I))) = 1) :
    ∃ r s Mi ki a M kappa A : ℝ, ∃ hs : 0 < s,
      0 < r ∧ 0 < Mi ∧ 0 < ki ∧ 0 < a ∧ 0 < M ∧ 0 < kappa ∧ 0 < A ∧
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
  obtain ⟨r, s, Mi, ki, ar, Mr, kr, hs, hr, hMi, hki, har, hMr, hkr, hd⟩ :=
    exists_actual_resonant_cycle_extraction hb hB hφ hπ hBi hbsq
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
  refine ⟨r, s, Mi, ki, a, Mr + Mn, kappa, A, hs, hr, hMi, hki, ha, add_pos hMr hMn, hk, hA,
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
