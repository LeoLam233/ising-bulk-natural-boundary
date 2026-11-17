import IsingBulk.AnisoF002.C03.IsotropicPhysicalIntegralPartition

/-!
# The original complete particle integral is the actual finite partition

The full physical balanced deformation is integrated first. Its exact
population split and reflection then give the mixed piece, every compact
right mean, and every named left anchor. No angular sector is omitted;
the same original factorial and 2 pi normalization remains in every term.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory

theorem exists_actual_complete_particle_partition (η : ℝ) (hη : 0 < η) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ n : ℕ, ∀ τ ∈ Icc 0 Δ,
      ∀ s σ : ℂ, 0 < s.im → ‖σ‖ ≤ 1 → ∀ b δ ρ a : ℝ, a = 0 ∨ a = Real.pi →
      (∫ x in angularIntegrationBox (n + 1),
        isotropicBarePhysicalDensity s σ (fun i => (affineConstraintAngles a x i : ℂ))) =
        actualWeightedParticleIntegral (n := n + 1) η τ 1 σ
          (fun θ => (mixedPopulationCutoff η θ : ℂ)) a s +
        2 * (actualWeightedParticleIntegral η τ 1 σ (actualLowerRightCutoff η b δ ρ (n + 2)) a s +
          ∑ i : Fin (n + 2), actualWeightedParticleIntegral η τ 1 σ
            (actualLowerAnchorCutoff η b δ ρ i) a s) := by
  obtain ⟨Δ, hΔ, hdef⟩ := exists_full_physical_balanced_deformation η hη
  refine ⟨Δ, hΔ, ?_⟩
  intro n τ hτ s σ hs hσ b δ ρ a ha
  have he : actualWeightedParticleIntegral (n := n + 1) η τ 1 σ (fun _ => 1) a s =
      ∫ x in angularIntegrationBox (n + 1),
        isotropicBarePhysicalDensity s σ (fun i => (affineConstraintAngles a x i : ℂ)) := by
    simpa only [actualWeightedParticleIntegral, one_mul, homotopyPulledDensity_actual] using
      hdef n τ hτ s hs σ hσ a
  rw [← he]
  exact actual_complete_integral_lower_partition s σ hs hσ η τ 1 b δ ρ hη hτ.1 zero_le_one a ha

theorem exists_actual_complete_compact_particle_partition (η : ℝ) (hη : 0 < η) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ n : ℕ, ∀ τ ∈ Icc 0 Δ,
      ∀ s σ : ℂ, 0 < s.im → ‖σ‖ ≤ 1 → ∀ b δ ρ β a : ℝ,
      RightCutoffGeometry b δ ρ → δ ≤ β → ρ + δ / 2 ≤ β → a = 0 ∨ a = Real.pi →
      (∫ x in angularIntegrationBox (n + 1),
        isotropicBarePhysicalDensity s σ (fun i => (affineConstraintAngles a x i : ℂ))) =
        actualWeightedParticleIntegral (n := n + 1) η τ 1 σ
          (fun θ => (mixedPopulationCutoff η θ : ℂ)) a s +
        2 * ((∑ l ∈ admissibleRightLifts (n + 2) b β a,
          ∫ x : Fin (n + 1) → ℝ,
            actualLowerCompactRightCutoff η b δ ρ (n + 2)
              (centeredConstraintAngles (constrainedRightMean (n + 2) b a l - b) x) *
            homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ)
              (1, centeredConstraintAngles (constrainedRightMean (n + 2) b a l - b) x)) +
          ∑ i : Fin (n + 2), actualWeightedParticleIntegral η τ 1 σ
            (actualLowerAnchorCutoff η b δ ρ i) a s) := by
  obtain ⟨Δ, hΔ, hpart⟩ := exists_actual_complete_particle_partition η hη
  refine ⟨Δ, hΔ, ?_⟩
  intro n τ hτ s σ hs hσ b δ ρ β a hcut hδ hρ ha
  rw [hpart n τ hτ s σ hs hσ b δ ρ a ha]
  have hh := actual_original_right_density_integral_centered_lifts hcut hδ hρ
    (n := n + 1) s σ hs hσ η τ 1 hη hτ.1 zero_le_one a
  change actualWeightedParticleIntegral η τ 1 σ (actualLowerRightCutoff η b δ ρ (n + 2)) a s = _ at hh
  rw [hh]

end IsingBulk.AnisoF002.Isotropic
