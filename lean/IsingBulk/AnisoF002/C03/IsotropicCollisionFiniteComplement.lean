import IsingBulk.AnisoF002.C03.IsotropicAwaySupportAllParticles
import IsingBulk.AnisoF002.C03.IsotropicCollisionCoefficientSplit

/-!
# The actual finite-particle complement for every particle N≥2

Every complex derivative of the literal smooth away-coincidence piece
has a logarithmic radial bound. The cutoff radius can be chosen after
the physical neighborhood, and the bound includes N=2 and N=3.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology BigOperators ContDiff

theorem exists_actual_all_particle_compact_mean_away_bound (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ δB ρB : ℝ, RightCutoffGeometry b δB ρB → δB ≤ β → ρB + δB / 2 ≤ β →
      ∀ n : ℕ, ∀ r : ℝ, 0 < r → ∀ j : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 → ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1,
      ∀ μ : ℝ, ∀ ε ∈ Ioo 0 δ,
        ‖iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ μ σ
          (weightedCollisionAway r (actualLowerCompactRightCutoff η b δB ρB (n + 2))))
          (isotropicRadialParameter α ε)‖ ≤ A * (1 + |Real.log ε|) := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_all_particle_away_support_bound α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, hδ, hδβ, hbnd⟩ := hdata η hη hwidth
  refine ⟨δ, hδ, hδβ, ?_⟩
  intro δB ρB hcut hδB hρB n r hr j
  apply hbnd n (weightedCollisionAway r (actualLowerCompactRightCutoff η b δB ρB (n + 2)))
    (weightedCollisionAway_contDiff r (actualLowerCompactRightCutoff_contDiff η b δB ρB (n + 2)))
  · intro θ ht k
    have hh := compactRightProduct_weighted_tsupport hcut
      (fun y : Fin (n + 2) → ℝ => (lowerPopulationCutoff η y : ℂ))
      (weightedCollisionAway_tsupport hr _ ht).1 k
    exact ⟨by linarith [hh.1], hh.2.trans hρB⟩
  · intro θ ht
    exact weightedCollisionAway_nonconstant (by omega) hr _ ht

end
end IsingBulk.AnisoF002.Isotropic
