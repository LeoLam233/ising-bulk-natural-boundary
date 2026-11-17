import IsingBulk.AnisoF002.C03.RegularModelExactLog
import IsingBulk.AnisoF002.NegativeHT.IntegerSelection
import IsingBulk.AnisoF002.NegativeHT.CenterPhaseLimit

/-!
# The exact integer-order recurrence of the actual first-winding model

The anisotropy and curvature are evaluated at their genuine winding
centers.  Their full complex phases remain in the model; only the exact
modulus identity is used to compare neighboring particle populations.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped Topology

def actualModelCrossing (B : ℂ → ℂ) (c s : ℝ) (n d j : ℕ) : ℝ :=
  actualModelLog B c s (n + 2 * d) j - actualModelLog B c s n j

theorem actualModelLog_eq_logMagnitude (B : ℂ → ℂ) (c : ℝ) {s : ℝ}
    {n : ℕ} (hn : 0 < n) (hs : 0 < s) (j : ℕ) :
    actualModelLog B c s n j = Real.log
      (modelMagnitude n j ‖B (windingTau n : ℂ)‖
        ‖firstWindingCurvature n (B (windingTau n : ℂ)) c s‖ s (windingTau n)) := by
  rw [actualModelLog, norm_modelCoefficient _ _ _ _ _ _ hn hs (windingTau_pos n hn)]

theorem particleExponent_mono {l r : ℕ} (hlr : l ≤ r) :
    particleExponent l ≤ particleExponent r := by
  have hpow := Nat.pow_le_pow_left hlr 2
  unfold particleExponent
  omega

theorem actualModelCrossing_order_step {B : ℂ → ℂ} {c s : ℝ} {n d j : ℕ}
    (hn : 0 < n) (hs : 0 < s)
    (hBl : B (windingTau n : ℂ) ≠ 0)
    (hBr : B (windingTau (n + 2 * d) : ℂ) ≠ 0)
    (hhl : firstWindingCurvature n (B (windingTau n : ℂ)) c s ≠ 0)
    (hhr : firstWindingCurvature (n + 2 * d) (B (windingTau (n + 2 * d) : ℂ)) c s ≠ 0)
    (hja : particleExponent (n + 2 * d) ≤ j) :
    actualModelCrossing B c s n d (j + 1) - actualModelCrossing B c s n d j =
      Real.log (windingTau n / windingTau (n + 2 * d)) +
      Real.log ((((j + 1 : ℕ) : ℝ) - particleExponent (n + 2 * d)) /
        (((j + 1 : ℕ) : ℝ) - particleExponent n)) := by
  have hrn : 0 < n + 2 * d := by omega
  have hal : particleExponent n ≤ j := (particleExponent_mono (by omega)).trans hja
  simp only [actualModelCrossing]
  simp_rw [actualModelLog_eq_logMagnitude B c hrn hs,
    actualModelLog_eq_logMagnitude B c hn hs]
  exact centered_log_ratio_order_step n (n + 2 * d) j
    ‖B (windingTau n : ℂ)‖ ‖firstWindingCurvature n (B (windingTau n : ℂ)) c s‖ s (windingTau n)
    ‖B (windingTau (n + 2 * d) : ℂ)‖
    ‖firstWindingCurvature (n + 2 * d) (B (windingTau (n + 2 * d) : ℂ)) c s‖ s
    (windingTau (n + 2 * d)) hn (norm_pos_iff.mpr hBl) (norm_pos_iff.mpr hhl) hs
    (windingTau_pos n hn) hrn (norm_pos_iff.mpr hBr) (norm_pos_iff.mpr hhr) hs
    (windingTau_pos _ hrn) hal hja

theorem actualModelCrossing_order_step_le {B : ℂ → ℂ} {c s : ℝ} {n d j : ℕ}
    (hn : 0 < n) (hs : 0 < s)
    (hBl : B (windingTau n : ℂ) ≠ 0)
    (hBr : B (windingTau (n + 2 * d) : ℂ) ≠ 0)
    (hhl : firstWindingCurvature n (B (windingTau n : ℂ)) c s ≠ 0)
    (hhr : firstWindingCurvature (n + 2 * d) (B (windingTau (n + 2 * d) : ℂ)) c s ≠ 0)
    (hja : particleExponent (n + 2 * d) ≤ j) :
    actualModelCrossing B c s n d (j + 1) - actualModelCrossing B c s n d j ≤
      Real.log (windingTau n / windingTau (n + 2 * d)) := by
  rw [actualModelCrossing_order_step hn hs hBl hBr hhl hhr hja]
  have hab : (particleExponent n : ℝ) ≤ particleExponent (n + 2 * d) := by
    exact_mod_cast (particleExponent_mono (show n ≤ n + 2 * d by omega))
  have haj : (particleExponent (n + 2 * d) : ℝ) < ((j + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show particleExponent (n + 2 * d) < j + 1 by omega)
  have hlog := (log_gamma_step_bounds ((j + 1 : ℕ) : ℝ)
    (particleExponent n) (particleExponent (n + 2 * d)) hab haj).2
  linarith

theorem eventually_actual_model_factors_ne_zero {B : ℂ → ℂ}
    (hB : ContinuousAt B 0) (hB0 : B 0 ≠ 0) (c s : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ B (windingTau n : ℂ) ≠ 0 ∧
      firstWindingCurvature n (B (windingTau n : ℂ)) c s ≠ 0 := by
  have hBn := (tendsto_anisotropy_at_centers B hB).eventually (eventually_ne_nhds hB0)
  filter_upwards [hBn, eventually_center_curvature_phase B hB c s,
    eventually_gt_atTop (0 : ℕ)] with n hnB hcurv hn
  refine ⟨hn, hnB, ?_⟩
  intro he
  have hpos := hcurv.1
  simp only [he, Complex.zero_re, lt_self_iff_false] at hpos

end
end IsingBulk.AnisoF002.NegativeHT
