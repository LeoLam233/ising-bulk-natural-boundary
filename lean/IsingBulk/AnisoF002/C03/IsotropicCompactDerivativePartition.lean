import IsingBulk.AnisoF002.C03.IsotropicCompactParticleHolomorphy
import IsingBulk.AnisoF002.C03.IsotropicPhysicalDerivativePartition

/-!
# Exact all-jet compact-mean decomposition of the full particle

Every actual compact mean is differentiated as its genuine holomorphic
coefficient. The finite mean sum and every named anchor are retained.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter MeasureTheory

theorem actual_right_parameter_jets_centered_lifts {b δ ρ β : ℝ}
    (hcut : RightCutoffGeometry b δ ρ) (hδ : δ ≤ β) (hρ : ρ + δ / 2 ≤ β)
    {n : ℕ} (η τ ξ a : ℝ) (σ S : ℂ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (hσ : ‖σ‖ ≤ 1) (hS : 0 < S.im) (j : ℕ) :
    iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ (actualLowerRightCutoff η b δ ρ (n + 1)) a) S =
      ∑ l ∈ admissibleRightLifts (n + 1) b β a,
        iteratedDeriv j (compactMeanPhysicalCoefficient n η τ ξ b δ ρ
          (constrainedRightMean (n + 1) b a l - b) σ) S := by
  have he : actualWeightedParticleIntegral η τ ξ σ (actualLowerRightCutoff η b δ ρ (n + 1)) a =ᶠ[𝓝 S]
      fun T => ∑ l ∈ admissibleRightLifts (n + 1) b β a,
        compactMeanPhysicalCoefficient n η τ ξ b δ ρ (constrainedRightMean (n + 1) b a l - b) σ T := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hS] with T hT
    exact actual_original_right_density_integral_centered_lifts hcut hδ hρ T σ hT hσ η τ ξ hη hτ hξ a
  rw [(he.iteratedDeriv j).eq_of_nhds]
  apply iteratedDeriv_fun_sum
  intro l _
  exact (compactMeanPhysicalCoefficient_analyticAt hcut n η τ ξ _ σ hη hτ hξ hσ S hS).contDiffAt

theorem exists_actual_complete_compact_derivative_partition (η : ℝ) (hη : 0 < η) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ n : ℕ, ∀ τ ∈ Icc 0 Δ, ∀ b δ ρ β a : ℝ,
      RightCutoffGeometry b δ ρ → δ ≤ β → ρ + δ / 2 ≤ β → a = 0 ∨ a = Real.pi →
      ∀ σ S : ℂ, ‖σ‖ ≤ 1 → 0 < S.im → ∀ j : ℕ,
      iteratedDeriv j (isotropicFullParticleCoefficient (n + 1) a σ) S =
        iteratedDeriv j (mixedPhysicalCoefficient (n + 1) η τ a σ) S +
        2 * ((∑ l ∈ admissibleRightLifts (n + 2) b β a,
          iteratedDeriv j (compactMeanPhysicalCoefficient (n + 1) η τ 1 b δ ρ
            (constrainedRightMean (n + 2) b a l - b) σ) S) +
          ∑ i : Fin (n + 2), iteratedDeriv j (actualWeightedParticleIntegral η τ 1 σ
            (actualLowerAnchorCutoff η b δ ρ i) a) S) := by
  obtain ⟨Δ, hΔ, hpart⟩ := exists_actual_complete_particle_derivative_partition η hη
  refine ⟨Δ, hΔ, ?_⟩
  intro n τ hτ b δ ρ β a hcut hδ hρ ha σ S hσ hS j
  rw [hpart n τ hτ b δ ρ a ha σ S hσ hS j,
    actual_right_parameter_jets_centered_lifts hcut hδ hρ η τ 1 a σ S hη hτ.1 zero_le_one hσ hS j]

end IsingBulk.AnisoF002.Isotropic
