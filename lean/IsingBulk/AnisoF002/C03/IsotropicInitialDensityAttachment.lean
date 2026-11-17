import IsingBulk.AnisoF002.C03.IsotropicTransportDensity
import IsingBulk.AnisoF002.C03.IsotropicFullPhysicalHomotopy

/-!
# Exact physical attachment of the initial complete transport density

The initial density in the actual regular frame is the original full
normalized physical density pulled through the full balanced homotopy,
with the same real angular cutoff. Every inverse-coordinate and
one-body cancellation condition is discharged on its actual image.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric
open scoped Topology BigOperators

theorem actualTransportedDensity_zero_physical {N : ℕ} (σ : ℂ) (η τ ξ : ℝ)
    (g : (Fin N → ℝ) → ℂ) (q : ℂ × (Fin N → ℝ))
    (hq : ∀ i, 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im)
    (hU : ∀ i, explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
      actualHomotopyAngle η τ ξ q.2 i)
    (hD : ∀ i, Complex.sin (actualPhysicalPhase η τ ξ q i) -
      Complex.sin (actualHomotopyAngle η τ ξ q.2 i) ≠ 0) :
    actualTransportedDensity σ η τ ξ g 0 q =
      g q.2 * homotopyPulledDensity η τ (isotropicBarePhysicalDensity q.1 σ) (ξ, q.2) := by
  have hh := actualInitialAmplitude_physical_density σ η τ ξ (fun y => g y.2) q hq hU hD
  change (actualCoordinateDeterminant η τ ξ q * actualSignedProductKernel σ η τ ξ q) *
    actualInitialAmplitude η τ ξ (fun y => g y.2) q = _
  rw [mul_assoc, hh, homotopyPulledDensity_actual]
  unfold isotropicBarePhysicalDensity
  change _ = g q.2 * ((actualBalancedJacobian η τ ξ q.2).det *
    (isotropicParticleNormalization N * _ * _ * _))
  dsimp only [actualPhysicalPhase]
  ring

theorem exists_actual_initial_density_attachment (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ), 0 < N →
      ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ η τ ξ : ℝ, 0 < η → τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-Real.pi - δ) δ) →
      ∀ σ : ℂ, ∀ g : (Fin N → ℝ) → ℂ,
        actualTransportedDensity σ η τ ξ g 0 (s, θ) =
          g θ * homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ) (ξ, θ) := by
  obtain ⟨δ, hδ, hinverse⟩ := exists_actual_oneSided_inverse_data S hS
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsd η τ ξ hη hτ hξ θ hθ σ g
  have hd := hinverse N hN s hs hsd η τ ξ hη hτ hξ θ hθ
  have hsheet (i : Fin N) := actual_balanced_homotopy_sheet s hs η τ ξ hη hτ.1 hξ.1 θ i
  apply actualTransportedDensity_zero_physical σ η τ ξ g (s, θ) hsheet
  · exact fun i => (hd i).2.2.2
  · intro i
    have hi := (hd i).2.2.1
    unfold explicitRightDenominator at hi
    rw [(hd i).2.2.2] at hi
    simpa only [actualPhysicalCoordinate, physicalRegularCoordinate, add_sub_cancel_left,
      actualPhysicalPhase] using hi

end
end IsingBulk.AnisoF002.Isotropic
