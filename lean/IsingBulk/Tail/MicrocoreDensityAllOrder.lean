import IsingBulk.Tail.MicrocoreFrozenAllOrder
import IsingBulk.Tail.MicrocoreDensity

/-! The literal source microcore density retains its complete Vandermonde
square and its simple Z denominator at every Lie order. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie
open scoped ContDiff

def microcoreVariableFactor {N : ℕ} (z : ℂ × (Fin N → ℂ)) : ℂ :=
  microRegularAmplitude z.1 z.2/(1-regularYProduct z.1 z.2)

theorem microRegularDensity_phase_factor {N : ℕ} (s : ℂ) (φ : Fin N → ℂ) :
    microRegularDensity s φ = microcorePhaseFactor φ*microcoreVariableFactor (s,φ) := by
  rw [microRegularDensity_unfactored]
  unfold microcorePhaseFactor microcoreVariableFactor regularKernel regularZProduct
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem microcore_weighted_density_factor {n : ℕ} (v θ : ℝ) (w : AngularSpace n → ℝ) :
    (fun s x => (w x:ℂ)*chartPullback v θ (@microRegularDensity (n+1)) s x) =
      (fun s x => microcorePhaseFactor (chartMap v θ s x)*
        ((w x:ℂ)*chartPullback v θ (fun t φ => microcoreVariableFactor (t,φ)) s x)) := by
  funext s x
  simp only [chartPullback,microRegularDensity_phase_factor]
  change (w x:ℂ)*(chartJacobian v θ s x*(microcorePhaseFactor (chartMap v θ s x)*
    microcoreVariableFactor (s,chartMap v θ s x))) =
      microcorePhaseFactor (chartMap v θ s x)*((w x:ℂ)*(chartJacobian v θ s x*
        microcoreVariableFactor (s,chartMap v θ s x)))
  ring

theorem microcore_density_all_order {n : ℕ} (v θ : ℝ) (w : AngularSpace n → ℝ)
    (U : Set ℂ) (R : Set (AngularSpace n)) (hU : IsOpen U) (hR : IsOpen R)
    (hw : ContDiff ℝ ∞ w) (hchart : ∀ s ∈ U, ∀ x ∈ R, MicrocoreJetPoint v θ s x)
    (hF : ∀ s ∈ U, ∀ x ∈ R, AnalyticAt ℂ microcoreVariableFactor (s,chartMap v θ s x))
    (hZ : ∀ s ∈ U, ∀ x ∈ R, 1-regularZProduct s (chartMap v θ s x) ≠ 0) (j : ℕ) :
    ∀ s ∈ U, ∀ x ∈ R,
      ((lieStep (microcoreField v θ))^[j]
        (fun t y => (w y:ℂ)*chartPullback v θ (@microRegularDensity (n+1)) t y)) s x =
      microcorePhaseFactor (chartMap v θ s x)*microcoreTermSum v θ w microcoreVariableFactor j s x := by
  rw [microcore_weighted_density_factor]
  exact microcore_frozen_factor_all_order v θ w microcoreVariableFactor microcorePhaseFactor
    U R hU hR hw hchart hF
    (fun s hs x hx => microcorePhaseFactor_differentiable _ (hZ s hs x hx)) j

end
end IsingBulk.Tail
