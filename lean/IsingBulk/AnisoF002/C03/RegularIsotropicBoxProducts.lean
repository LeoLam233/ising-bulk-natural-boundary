import IsingBulk.AnisoF002.C03.RegularIsotropicPositivePeriod
import IsingBulk.AnisoF002.C03.IsotropicFullPhysicalHomotopy
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Exact independent-angle integration of the true one-body majorant

The measure here is the original Lebesgue product on [0,2 pi]^n.
No orthonormal hyperplane normalization or probability measure is
substituted for it.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators

theorem angularIntegrationBox_restrict (n : ℕ) :
    volume.restrict (angularIntegrationBox n) =
      Measure.pi (fun _ : Fin n => volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) := by
  change (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict _ = _
  rw [angularIntegrationBox, ← Set.pi_univ_Icc, Measure.restrict_pi_pi]
  rfl

theorem angularIntegrationBox_product_integral (n : ℕ) (f : ℝ → ℝ) :
    (∫ x in angularIntegrationBox n, ∏ i, f (x i)) =
      (∫ θ in Icc (0 : ℝ) (2 * Real.pi), f θ) ^ n := by
  rw [angularIntegrationBox_restrict]
  simpa only [Fintype.card_fin] using
    (integral_fintype_prod_eq_pow (ι := Fin n) (μ := volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) f)

theorem angularIntegrationBox_product_integrable (n : ℕ) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc (0 : ℝ) (2 * Real.pi)) volume) :
    IntegrableOn (fun x : Fin n → ℝ => ∏ i, f (x i)) (angularIntegrationBox n) volume := by
  unfold IntegrableOn
  rw [angularIntegrationBox_restrict]
  exact Integrable.fintype_prod (fun _ : Fin n => hf)

theorem angularIntegrationBox_product_integral_bound (n : ℕ) {f : ℝ → ℝ} {L : ℝ}
    (hf : ∀ θ, 0 ≤ f θ) (hL : (∫ θ in Icc (0 : ℝ) (2 * Real.pi), f θ) ≤ L) :
    (∫ x in angularIntegrationBox n, ∏ i, f (x i)) ≤ L ^ n := by
  rw [angularIntegrationBox_product_integral]
  exact pow_le_pow_left₀ (integral_nonneg hf) hL n

end
end IsingBulk.AnisoF002.Isotropic
