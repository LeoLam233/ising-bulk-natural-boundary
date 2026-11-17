import IsingBulk.AnisoF002.C03.IsotropicCollisionPartition

/-!
# Exact physical near/away coefficient splitting and its controlled complement

The split is performed after the full physical deformation. Both pieces
are genuine whole-space centered coefficients, every complex derivative
splits exactly, and the actual away piece has the proved logarithmic
bound at every fixed derivative order.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

theorem centeredWeightedPhysicalCoefficient_integrable {n : ℕ}
    (η τ ξ μ : ℝ) (σ : ℂ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hσ : ‖σ‖ ≤ 1)
    (g : (Fin (n + 1) → ℝ) → ℂ) (hg : Continuous g) {L U : ℝ}
    (hsupp : ∀ θ ∈ tsupport g, ∀ k, θ k ∈ Icc L U) (S : ℂ) (hS : 0 < S.im) :
    Integrable (fun x : Fin n → ℝ => g (centeredConstraintAngles μ x) *
      homotopyPulledDensity η τ (isotropicBarePhysicalDensity S σ) (ξ, centeredConstraintAngles μ x)) := by
  have hs : Function.support g ⊆ Icc (fun _ => L) (fun _ => U) := by
    intro θ ht
    have hh := hsupp θ (subset_closure ht)
    exact ⟨fun k => (hh k).1, fun k => (hh k).2⟩
  simpa only [iteratedDeriv_zero] using
    ((centeredWeightedPhysicalCoefficient_analytic_and_jets η τ ξ μ σ hη hτ hξ hσ g hg hs S hS).2 0).1

theorem centeredWeightedPhysicalCoefficient_collision_split {n : ℕ}
    (η τ ξ μ r : ℝ) (σ : ℂ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hσ : ‖σ‖ ≤ 1)
    (g : (Fin (n + 1) → ℝ) → ℂ) (hg : ContDiff ℝ ∞ g) {L U : ℝ}
    (hsupp : ∀ θ ∈ tsupport g, ∀ k, θ k ∈ Icc L U) (S : ℂ) (hS : 0 < S.im) :
    centeredWeightedPhysicalCoefficient η τ ξ μ σ g S =
      centeredWeightedPhysicalCoefficient η τ ξ μ σ (weightedCollisionNear r g) S +
      centeredWeightedPhysicalCoefficient η τ ξ μ σ (weightedCollisionAway r g) S := by
  have hnear := centeredWeightedPhysicalCoefficient_integrable η τ ξ μ σ hη hτ hξ hσ
    (weightedCollisionNear r g) (weightedCollisionNear_contDiff r hg).continuous
    (fun θ ht => hsupp θ (tsupport_mul_subset_left ht)) S hS
  have haway := centeredWeightedPhysicalCoefficient_integrable η τ ξ μ σ hη hτ hξ hσ
    (weightedCollisionAway r g) (weightedCollisionAway_contDiff r hg).continuous
    (fun θ ht => hsupp θ (tsupport_mul_subset_left ht)) S hS
  unfold centeredWeightedPhysicalCoefficient
  rw [← integral_add hnear haway]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [← add_mul, ← weightedCollision_exact_split]

theorem centeredWeightedPhysicalCoefficient_collision_jets {n : ℕ}
    (η τ ξ μ r : ℝ) (σ : ℂ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hσ : ‖σ‖ ≤ 1)
    (g : (Fin (n + 1) → ℝ) → ℂ) (hg : ContDiff ℝ ∞ g) {L U : ℝ}
    (hsupp : ∀ θ ∈ tsupport g, ∀ k, θ k ∈ Icc L U) (S : ℂ) (hS : 0 < S.im) (j : ℕ) :
    iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ μ σ g) S =
      iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ μ σ (weightedCollisionNear r g)) S +
      iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ μ σ (weightedCollisionAway r g)) S := by
  have hsupports (f : (Fin (n + 1) → ℝ) → ℂ) (hf : tsupport f ⊆ tsupport g) :
      Function.support f ⊆ Icc (fun _ => L) (fun _ => U) := by
    intro θ ht
    have hh := hsupp θ (hf (subset_closure ht))
    exact ⟨fun k => (hh k).1, fun k => (hh k).2⟩
  have hnear : ContDiffAt ℂ j (centeredWeightedPhysicalCoefficient η τ ξ μ σ (weightedCollisionNear r g)) S :=
    (centeredWeightedPhysicalCoefficient_analytic_and_jets η τ ξ μ σ hη hτ hξ hσ
      (weightedCollisionNear r g) (weightedCollisionNear_contDiff r hg).continuous
      (hsupports _ tsupport_mul_subset_left) S hS).1.contDiffAt
  have haway : ContDiffAt ℂ j (centeredWeightedPhysicalCoefficient η τ ξ μ σ (weightedCollisionAway r g)) S :=
    (centeredWeightedPhysicalCoefficient_analytic_and_jets η τ ξ μ σ hη hτ hξ hσ
      (weightedCollisionAway r g) (weightedCollisionAway_contDiff r hg).continuous
      (hsupports _ tsupport_mul_subset_left) S hS).1.contDiffAt
  have he : centeredWeightedPhysicalCoefficient η τ ξ μ σ g =ᶠ[𝓝 S]
      fun T => centeredWeightedPhysicalCoefficient η τ ξ μ σ (weightedCollisionNear r g) T +
        centeredWeightedPhysicalCoefficient η τ ξ μ σ (weightedCollisionAway r g) T := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hS] with T hT
    exact centeredWeightedPhysicalCoefficient_collision_split η τ ξ μ r σ hη hτ hξ hσ g hg hsupp T hT
  rw [(he.iteratedDeriv j).eq_of_nhds, iteratedDeriv_fun_add hnear haway]

theorem actual_compact_mean_collision_jets {b δB ρB : ℝ}
    (hcut : RightCutoffGeometry b δB ρB) (n : ℕ) (η τ ξ μ r : ℝ) (σ : ℂ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hσ : ‖σ‖ ≤ 1)
    (S : ℂ) (hS : 0 < S.im) (j : ℕ) :
    iteratedDeriv j (compactMeanPhysicalCoefficient n η τ ξ b δB ρB μ σ) S =
      iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ μ σ
        (weightedCollisionNear r (actualLowerCompactRightCutoff η b δB ρB (n + 1)))) S +
      iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ μ σ
        (weightedCollisionAway r (actualLowerCompactRightCutoff η b δB ρB (n + 1)))) S := by
  exact centeredWeightedPhysicalCoefficient_collision_jets η τ ξ μ r σ hη hτ hξ hσ
    (actualLowerCompactRightCutoff η b δB ρB (n + 1))
    (actualLowerCompactRightCutoff_contDiff η b δB ρB (n + 1))
    (fun θ ht k => compactRightProduct_weighted_tsupport hcut
      (fun y : Fin (n + 1) → ℝ => (lowerPopulationCutoff η y : ℂ)) ht k) S hS j

theorem exists_actual_compact_mean_away_bound (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ δB ρB : ℝ, RightCutoffGeometry b δB ρB → δB ≤ β → ρB + δB / 2 ≤ β →
      ∀ n : ℕ, ∀ r : ℝ, 0 < r → ∀ j : ℕ, ∃ A : ℝ, 0 < A ∧
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 → ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1,
      ∀ μ : ℝ, ∀ ε ∈ Ioo 0 δ,
        ‖iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ μ σ
          (weightedCollisionAway r (actualLowerCompactRightCutoff η b δB ρB (n + 4))))
          (isotropicRadialParameter α ε)‖ ≤ A * (1 + |Real.log ε|) := by
  obtain ⟨β, hβ, hβ1, hdata⟩ := exists_actual_away_support_logarithmic_bound α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, hδ, hδβ, hbnd⟩ := hdata η hη hwidth
  refine ⟨δ, hδ, hδβ, ?_⟩
  intro δB ρB hcut hδB hρB n r hr j
  apply hbnd n (weightedCollisionAway r (actualLowerCompactRightCutoff η b δB ρB (n + 4)))
    (weightedCollisionAway_contDiff r (actualLowerCompactRightCutoff_contDiff η b δB ρB (n + 4)))
  · intro θ ht k
    have hh := compactRightProduct_weighted_tsupport hcut
      (fun y : Fin (n + 4) → ℝ => (lowerPopulationCutoff η y : ℂ))
      (weightedCollisionAway_tsupport hr _ ht).1 k
    exact ⟨by linarith [hh.1], hh.2.trans hρB⟩
  · intro θ ht
    exact weightedCollisionAway_nonconstant (by omega) hr _ ht

end
end IsingBulk.AnisoF002.Isotropic
