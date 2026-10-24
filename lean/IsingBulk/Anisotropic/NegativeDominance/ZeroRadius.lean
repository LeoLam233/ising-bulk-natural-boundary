import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Tactic

/-! The last analytic obstruction in ANISO Theorem 5.5, stated for actual
Taylor coefficients. No claim here supplies the required coefficient growth
for the susceptibility; that remains a separate all-index estimate. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped NNReal ENNReal

/-- Unbounded scaled coefficients at every positive radius force zero radius. -/
theorem scalar_radius_eq_zero_of_unbounded (a : ℕ → ℂ)
    (hu : ∀ r : ℝ, 0 < r → ∀ C : ℝ, ∃ n, C < ‖a n‖ * r ^ n) :
    (FormalMultilinearSeries.ofScalars ℂ a).radius = 0 := by
  apply le_antisymm _ (by positivity)
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  by_contra hnot
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (lt_of_not_ge hnot)
  obtain ⟨C, _, hC⟩ :=
    (FormalMultilinearSeries.ofScalars ℂ a).norm_mul_pow_le_of_lt_radius hr
  obtain ⟨n, hn⟩ := hu r hrpos C
  have hc := hC n
  rw [FormalMultilinearSeries.ofScalars_norm] at hc
  exact (not_lt_of_ge hc) hn

/-- A selected unbounded sequence is enough; no positivity or phase
alignment between distinct particle indices is required. -/
theorem scalar_radius_eq_zero_of_subsequence (a : ℕ → ℂ) (j : ℕ → ℕ)
    (hu : ∀ r : ℝ, 0 < r → ∀ C : ℝ, ∃ n, C < ‖a (j n)‖ * r ^ j n) :
    (FormalMultilinearSeries.ofScalars ℂ a).radius = 0 := by
  apply scalar_radius_eq_zero_of_unbounded
  intro r hr C
  obtain ⟨n, hn⟩ := hu r hr C
  exact ⟨j n, hn⟩

/-- A zero-radius scalar coefficient series cannot be the Taylor series of
any analytic germ, at any center. Identification with inward boundary jets
must be established before this theorem is applied. -/
theorem not_hasFPowerSeriesAt_of_zero_radius (a : ℕ → ℂ)
    (hz : (FormalMultilinearSeries.ofScalars ℂ a).radius = 0)
    (f : ℂ → ℂ) (z : ℂ) :
    ¬ HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) z := by
  intro hf
  have hp := hf.radius_pos
  rw [hz] at hp
  exact (lt_irrefl 0) hp

end
end IsingBulk.Anisotropic.NegativeDominance
