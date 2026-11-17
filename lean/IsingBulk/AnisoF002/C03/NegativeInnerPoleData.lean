import IsingBulk.AnisoF002.C03.NegativeInnerAngularCut

/-!
# Constructed inner poles on the full real angular torus

The pole is selected through a continuous unsigned coordinate while its
phase and all physical factors remain evaluated at the original real
tuple.  The closed angular cutoff includes every winding sector and gives
continuous pole data suitable for exact compact real-cycle integration.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

def realPhaseAverage (B : ℂ → ℂ) (φ : ℝ) (n : ℕ) (q : Fin n → ℝ) : ℂ → ℂ :=
  centeredPhaseAverage n (negativeGlobalPhase B φ) ((φ : ℂ) * Complex.I) 0 (fun i => (q i : ℂ))

def realPhaseTotal (B : ℂ → ℂ) (φ : ℝ) (n : ℕ) (q : Fin n → ℝ) (t : ℂ) : ℂ :=
  ∑ i, negativeGlobalPhase B φ (t, (q i : ℂ))

structure InnerPoleData (B : ℂ → ℂ) (φ : ℝ) (n : ℕ) (R s C : ℝ) (a : ℂ) where
  pole : (Fin n → ℝ) → ℂ
  pole_continuous : ContinuousOn pole {q | angularShortSquare q ≤ s}
  pole_zero : ∀ q, angularShortSquare q ≤ s → realPhaseAverage B φ n q (pole q) = 0
  pole_half : ∀ q, angularShortSquare q ≤ s → ‖pole q‖ ≤ R / 2
  pole_bound : ∀ q, angularShortSquare q ≤ s → ‖pole q‖ ≤ C * angularShortSquare q / (n : ℝ)
  average_analytic : ∀ q, angularShortSquare q ≤ s →
    AnalyticOnNhd ℂ (realPhaseAverage B φ n q) (Metric.closedBall (0 : ℂ) R)
  factor_analytic : ∀ q, angularShortSquare q ≤ s →
    AnalyticOnNhd ℂ (dslope (realPhaseAverage B φ n q) (pole q)) (Metric.ball (0 : ℂ) R)
  phase_factor : ∀ q, angularShortSquare q ≤ s → ∀ t ∈ Metric.closedBall (0 : ℂ) R,
    realPhaseTotal B φ n q t = (n : ℂ) * ((φ : ℂ) * Complex.I) +
      (n : ℂ) * (t - pole q) * dslope (realPhaseAverage B φ n q) (pole q) t
  factor_bounds : ∀ q, angularShortSquare q ≤ s → ∀ t ∈ Metric.closedBall (0 : ℂ) R,
    ‖a‖ / 2 ≤ ‖dslope (realPhaseAverage B φ n q) (pole q) t‖ ∧
      ‖dslope (realPhaseAverage B φ n q) (pole q) t‖ ≤ 3 * ‖a‖ / 2 ∧
      dslope (realPhaseAverage B φ n q) (pole q) t ≠ 0

theorem exists_actual_inner_pole_data {B : ℂ → ℂ} {φ : ℝ}
    (hB : AnalyticAt ℂ B 0) (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0) :
    ∃ R s C : ℝ, ∃ a : ℂ, 0 < R ∧ 0 < s ∧ 0 < C ∧
      a = fderiv ℂ (negativeGlobalPhase B φ) (0, 0) (1, 0) ∧ a ≠ 0 ∧
      ∀ n : ℕ, 0 < n → Nonempty (InnerPoleData B φ n R s C a) := by
  classical
  obtain ⟨R, σ, C, hR, hσ, hC, ha, hall⟩ := exists_actual_all_angle_phase_factors hB hφ hπ hBi
  let a := fderiv ℂ (negativeGlobalPhase B φ) (0, 0) (1, 0)
  let s := σ ^ 2 / 4
  have hs : 0 < s := by dsimp [s]; positivity
  refine ⟨R, s, C, a, hR, hs, hC, rfl, ha, ?_⟩
  intro n hn
  obtain ⟨T, hTa, _, hT⟩ := hall n hn
  let P : (Fin n → ℝ) → ℂ := fun q => T (complexUnsignedAngles q)
  have hsmall (q : Fin n → ℝ) (hq : angularShortSquare q ≤ s) :
      complexUnsignedAngles q ∈ Metric.ball 0 σ := by
    apply complexUnsignedAngles_mem_ball hσ
    dsimp [s] at hq
    nlinarith [sq_pos_of_pos hσ]
  have hF (q : Fin n → ℝ) :
      centeredPhaseAverage n (negativeGlobalPhase B φ) ((φ : ℂ) * Complex.I) 0
        (complexUnsignedAngles q) = realPhaseAverage B φ n q := by
    funext t
    exact centeredPhaseAverage_unsigned B φ n q ((φ : ℂ) * Complex.I) t
  have hdata (q : Fin n → ℝ) (hq : angularShortSquare q ≤ s) := hT _ (hsmall q hq)
  refine ⟨{
    pole := P
    pole_continuous := hTa.continuousOn.comp (complexUnsignedAngles_continuous n).continuousOn hsmall
    pole_zero := ?_
    pole_half := ?_
    pole_bound := ?_
    average_analytic := ?_
    factor_analytic := ?_
    phase_factor := ?_
    factor_bounds := ?_ }⟩
  · intro q hq
    simpa only [hF] using (hdata q hq).1
  · intro q hq
    exact (hdata q hq).2.1
  · intro q hq
    simpa only [complexUnsignedAngles_displacement] using (hdata q hq).2.2.1
  · intro q hq
    simpa only [hF] using (hdata q hq).2.2.2.1
  · intro q hq
    simpa only [hF] using (hdata q hq).2.2.2.2.1
  · intro q hq t ht
    have he := ((hdata q hq).2.2.2.2.2 t ht).1
    simpa only [realPhaseTotal, hF, complexUnsignedAngles, negativeGlobalPhase_unsigned] using he
  · intro q hq t ht
    have he := ((hdata q hq).2.2.2.2.2 t ht).2.2
    simpa only [hF] using he

end
end IsingBulk.AnisoF002.NegativeHT
