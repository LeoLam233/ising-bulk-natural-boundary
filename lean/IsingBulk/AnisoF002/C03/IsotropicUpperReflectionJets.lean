import IsingBulk.AnisoF002.C03.IsotropicUpperReflectionCutoffs

/-!
# Every parameter jet of the upper physical terms

The exact function identities precede differentiation. They therefore
transfer all complex parameter jets and every radial parametrization,
with the original signed kernel and original integration box unchanged.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic

theorem actual_upper_right_anchor_physical_functions {n : ℕ} (η τ ξ b δ ρ : ℝ)
    (σ : ℂ) (a : ℝ) (ha : a = 0 ∨ a = Real.pi) :
    actualWeightedParticleIntegral η τ ξ σ (actualUpperRightCutoff η b δ ρ (n + 1)) a =
      actualWeightedParticleIntegral η τ ξ σ (actualLowerRightCutoff η b δ ρ (n + 1)) a ∧
      ∀ i : Fin (n + 1),
        actualWeightedParticleIntegral η τ ξ σ (actualUpperAnchorCutoff η b δ ρ i) a =
          actualWeightedParticleIntegral η τ ξ σ (actualLowerAnchorCutoff η b δ ρ i) a := by
  constructor
  · have he : actualUpperRightCutoff η b δ ρ (n + 1) =
        fun θ => actualLowerRightCutoff η b δ ρ (n + 1) (fun i => -θ i) :=
      funext (actualUpperRightCutoff_reflection η b δ ρ (n + 1))
    rw [he]
    exact funext (fun s => actualWeightedParticleIntegral_physical_reflection η τ ξ s σ _
      (actualLowerRightCutoff_toroidal η b δ ρ) a ha)
  · intro i
    have he : actualUpperAnchorCutoff η b δ ρ i =
        fun θ => actualLowerAnchorCutoff η b δ ρ i (fun j => -θ j) :=
      funext (actualUpperAnchorCutoff_reflection η b δ ρ i)
    rw [he]
    exact funext (fun s => actualWeightedParticleIntegral_physical_reflection η τ ξ s σ _
      (actualLowerAnchorCutoff_toroidal η b δ ρ i) a ha)

theorem actual_upper_population_physical_functions {n : ℕ} (η τ ξ : ℝ)
    (σ : ℂ) (a : ℝ) (ha : a = 0 ∨ a = Real.pi) :
    actualWeightedParticleIntegral (n := n) η τ ξ σ (fun θ => (upperPopulationCutoff η θ : ℂ)) a =
      actualWeightedParticleIntegral (n := n) η τ ξ σ (fun θ => (lowerPopulationCutoff η θ : ℂ)) a := by
  have he : (fun θ : Fin (n + 1) → ℝ => (upperPopulationCutoff η θ : ℂ)) =
      fun θ => (lowerPopulationCutoff η (fun i => -θ i) : ℂ) := by
    funext θ
    rw [(actual_population_partition_reflection η θ).2.1]
  rw [he]
  exact funext (fun s => actualWeightedParticleIntegral_physical_reflection η τ ξ s σ
    (fun θ : Fin (n + 1) → ℝ => (lowerPopulationCutoff η θ : ℂ))
    (fun k θ => by rw [lowerPopulationCutoff_toroidal]) a ha)

theorem actual_upper_right_anchor_parameter_jets {n : ℕ} (η τ ξ b δ ρ : ℝ)
    (σ : ℂ) (a : ℝ) (ha : a = 0 ∨ a = Real.pi) (j : ℕ) (s : ℂ) :
    iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ
      (actualUpperRightCutoff η b δ ρ (n + 1)) a) s =
      iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ
        (actualLowerRightCutoff η b δ ρ (n + 1)) a) s ∧
      ∀ i : Fin (n + 1),
        iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ (actualUpperAnchorCutoff η b δ ρ i) a) s =
          iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ (actualLowerAnchorCutoff η b δ ρ i) a) s := by
  obtain ⟨hr, ha⟩ := actual_upper_right_anchor_physical_functions (n := n) η τ ξ b δ ρ σ a ha
  exact ⟨by rw [hr], fun i => by rw [ha i]⟩

theorem actual_upper_right_anchor_radial_jets {n : ℕ} (η τ ξ b δ ρ : ℝ)
    (σ : ℂ) (a : ℝ) (ha : a = 0 ∨ a = Real.pi) (S : ℝ → ℂ) (j : ℕ) (ε : ℝ) :
    iteratedDeriv j (fun t => actualWeightedParticleIntegral η τ ξ σ
      (actualUpperRightCutoff η b δ ρ (n + 1)) a (S t)) ε =
      iteratedDeriv j (fun t => actualWeightedParticleIntegral η τ ξ σ
        (actualLowerRightCutoff η b δ ρ (n + 1)) a (S t)) ε ∧
      ∀ i : Fin (n + 1),
        iteratedDeriv j (fun t => actualWeightedParticleIntegral η τ ξ σ
          (actualUpperAnchorCutoff η b δ ρ i) a (S t)) ε =
          iteratedDeriv j (fun t => actualWeightedParticleIntegral η τ ξ σ
            (actualLowerAnchorCutoff η b δ ρ i) a (S t)) ε := by
  obtain ⟨hr, ha⟩ := actual_upper_right_anchor_physical_functions (n := n) η τ ξ b δ ρ σ a ha
  exact ⟨by rw [hr], fun i => by rw [ha i]⟩

end IsingBulk.AnisoF002.Isotropic
