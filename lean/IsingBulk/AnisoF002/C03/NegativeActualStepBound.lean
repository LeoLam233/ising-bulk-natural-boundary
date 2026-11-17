import IsingBulk.AnisoF002.C03.NegativeActualOrderStep
import IsingBulk.AnisoF002.C03.RegularModelCorrections

/-!
# The actual O(1/N) integer crossing increment

The temperature ratio is estimated from its exact logarithmic filling.
All nonzero anisotropy/curvature and size gates are then discharged
eventually from the genuine analytic local factor.  The resulting step
bound is uniform in the full Taylor-order range used by first crossing.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped Topology

theorem actual_tau_ratio_bound_of_correction {n d : ℕ} {C : ℝ}
    (hn : 0 < n) (hC : 0 ≤ C) (hx1 : 1 ≤ (n : ℝ) + d)
    (hstep : (d : ℝ) ≤ ((n : ℝ) + d) / 4)
    (he : |actualTemperatureCorrection (n + 2 * d) - actualTemperatureCorrection n| ≤
      C * (d : ℝ) / ((n : ℝ) + d) ^ 3) :
    Real.log (windingTau n / windingTau (n + 2 * d)) ≤
      (8 + C) * (d : ℝ) / ((n : ℝ) + d) := by
  let x : ℝ := (n : ℝ) + d
  have hx : 0 < x := by dsimp [x]; linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrn : 0 < n + 2 * d := by omega
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hl := (log_increment_bounds hnR (show (0 : ℝ) ≤ 2 * d by positivity)).2
  have hl' : Real.log ((n + 2 * d : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 4 * (d : ℝ) / x := by
    apply le_trans (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hl)
    apply (div_le_div_iff₀ hnR hx).mpr
    dsimp [x] at *
    nlinarith [mul_nonneg hd0 (show (0 : ℝ) ≤ (n : ℝ) - d by linarith)]
  have hx2 : 1 ≤ x ^ 2 := by dsimp [x]; nlinarith
  have hx3 : x ≤ x ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hx2 hx.le]
  have he' : |actualTemperatureCorrection (n + 2 * d) - actualTemperatureCorrection n| ≤
      C * (d : ℝ) / x :=
    he.trans (div_le_div_of_nonneg_left (mul_nonneg hC hd0) hx hx3)
  have hleft := inverseParticleLogTemperature_reciprocal_re n hn
  have hright := inverseParticleLogTemperature_reciprocal_re (n + 2 * d) hrn
  change actualTemperatureCorrection n = _ at hleft
  change actualTemperatureCorrection (n + 2 * d) = _ at hright
  rw [Real.log_div (windingTau_pos n hn).ne' (windingTau_pos _ hrn).ne']
  have hneg := (abs_le.mp he').1
  change _ ≤ (8 + C) * (d : ℝ) / x
  have hratio : (8 + C) * (d : ℝ) / x = 2 * (4 * (d : ℝ) / x) + C * (d : ℝ) / x := by ring
  rw [hratio]
  linarith

theorem exists_actual_tau_ratio_step_bound {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0)
    (hslit : B 0 ∈ Complex.slitPlane) (c s : ℝ) :
    ∃ K R : ℝ, 0 < K ∧ 0 < R ∧
      ∀ n d : ℕ, Odd n → Even d → R ≤ (n : ℝ) + d →
        (d : ℝ) ≤ ((n : ℝ) + d) / 4 →
        Real.log (windingTau n / windingTau (n + 2 * d)) ≤
          K * (d : ℝ) / ((n : ℝ) + d) := by
  obtain ⟨C, R, hC, hR, hdiff⟩ := actual_model_correction_differences hB hslit c s
  refine ⟨8 + C, max R 1, by linarith, lt_of_lt_of_le hR (le_max_left _ _), ?_⟩
  intro n d hn hd hlarge hstep
  exact actual_tau_ratio_bound_of_correction hn.pos hC.le
    ((le_max_right _ _).trans hlarge) hstep
    (hdiff n d hn hd ((le_max_left _ _).trans hlarge) hstep).2.2.1

theorem exists_actual_order_step_upper_bound {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0)
    (hslit : B 0 ∈ Complex.slitPlane) (c : ℝ) {s : ℝ} (hs : 0 < s) :
    ∃ K R : ℝ, 0 < K ∧ 0 < R ∧
      ∀ n d : ℕ, Odd n → Even d → R ≤ (n : ℝ) + d →
        (d : ℝ) ≤ ((n : ℝ) + d) / 4 → ∀ j : ℕ,
        particleExponent (n + 2 * d) ≤ j →
        actualModelCrossing B c s n d (j + 1) - actualModelCrossing B c s n d j ≤
          K * (d : ℝ) / ((n : ℝ) + d) := by
  obtain ⟨K, R, hK, hR, hτ⟩ := exists_actual_tau_ratio_step_bound hB hslit c s
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_actual_model_factors_ne_zero hB.continuousAt (Complex.slitPlane_ne_zero hslit) c s)
  refine ⟨K, max R (4 * (N : ℝ) + 4), hK, lt_of_lt_of_le hR (le_max_left _ _), ?_⟩
  intro n d hn hd hlarge hstep j hj
  have hnlarge : N ≤ n := by
    have hNlarge := (le_max_right R (4 * (N : ℝ) + 4)).trans hlarge
    have hh : (N : ℝ) ≤ n := by nlinarith
    exact_mod_cast hh
  have hl := hN n hnlarge
  have hr := hN (n + 2 * d) (by omega)
  exact (actualModelCrossing_order_step_le hl.1 hs hl.2.1 hr.2.1 hl.2.2 hr.2.2 hj).trans
    (hτ n d hn hd ((le_max_left _ _).trans hlarge) hstep)

end
end IsingBulk.AnisoF002.NegativeHT
