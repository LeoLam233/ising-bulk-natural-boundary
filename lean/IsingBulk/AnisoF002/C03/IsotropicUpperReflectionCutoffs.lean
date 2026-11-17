import IsingBulk.AnisoF002.C03.IsotropicUpperReflectionIntegral

/-!
# Literal upper-population right and anchor terms

These are the actual reflected smooth cutoffs, with the upper raw
population factor retained. Reflection transfers their full normalized
physical integrals and every parameter jet to the lower terms at the
opposite total angle. The physical constraints 0 and pi are unchanged
modulo a full angular period.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory

def actualUpperRightCutoff (η b δ ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) : ℂ :=
  (upperPopulationCutoff η θ : ℂ) * rightCutoffProduct b δ ρ N (fun i => -θ i)

def actualUpperAnchorCutoff (η b δ ρ : ℝ) {N : ℕ} (a : Fin N) (θ : Fin N → ℝ) : ℂ :=
  (upperPopulationCutoff η θ : ℂ) * rightCutoffAnchor b δ ρ a (fun i => -θ i)

def actualUpperCompactRightCutoff (η b δ ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) : ℂ :=
  (upperPopulationCutoff η θ : ℂ) * compactRightProduct b δ ρ N (fun i => -θ i)

theorem actualUpperRightCutoff_reflection (η b δ ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) :
    actualUpperRightCutoff η b δ ρ N θ = actualLowerRightCutoff η b δ ρ N (fun i => -θ i) := by
  rw [actualUpperRightCutoff, actualLowerRightCutoff, (actual_population_partition_reflection η θ).2.1]

theorem actualUpperAnchorCutoff_reflection (η b δ ρ : ℝ) {N : ℕ} (a : Fin N) (θ : Fin N → ℝ) :
    actualUpperAnchorCutoff η b δ ρ a θ = actualLowerAnchorCutoff η b δ ρ a (fun i => -θ i) := by
  rw [actualUpperAnchorCutoff, actualLowerAnchorCutoff, (actual_population_partition_reflection η θ).2.1]

theorem actualUpperCompactRightCutoff_reflection (η b δ ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) :
    actualUpperCompactRightCutoff η b δ ρ N θ =
      actualLowerCompactRightCutoff η b δ ρ N (fun i => -θ i) := by
  rw [actualUpperCompactRightCutoff, actualLowerCompactRightCutoff,
    (actual_population_partition_reflection η θ).2.1]

theorem actual_upper_right_anchor_partition (η b δ ρ : ℝ) (N : ℕ) (θ : Fin N → ℝ) :
    (upperPopulationCutoff η θ : ℂ) = actualUpperRightCutoff η b δ ρ N θ +
      ∑ a, actualUpperAnchorCutoff η b δ ρ a θ := by
  simpa only [actualUpperRightCutoff_reflection, actualUpperAnchorCutoff_reflection,
    (actual_population_partition_reflection η θ).2.1] using
      actual_lower_right_anchor_partition η b δ ρ N (fun i => -θ i)

theorem actual_upper_right_anchor_jets (η b δ ρ : ℝ) (k : ℕ) :
    ∃ A C : ℝ, 1 ≤ A ∧ 1 ≤ C ∧ ∀ N : ℕ, 0 < N →
      FiniteJetControl k (actualUpperRightCutoff η b δ ρ N)
        (A * C ^ N * (N : ℝ) ^ (2 * k)) ∧
      ∀ a : Fin N, FiniteJetControl k (actualUpperAnchorCutoff η b δ ρ a)
        (A * C ^ N * (N : ℝ) ^ (2 * k)) := by
  obtain ⟨A, C, hA, hC, hbound⟩ := actual_lower_right_anchor_jets η b δ ρ k
  refine ⟨A, C, hA, hC, ?_⟩
  intro N hN
  let L := -(ContinuousLinearMap.id ℝ (Fin N → ℝ))
  have hL : ‖L‖ ≤ 1 := by
    dsimp [L]
    rw [norm_neg]
    exact ContinuousLinearMap.norm_id_le
  have hright : actualUpperRightCutoff η b δ ρ N =
      fun θ => actualLowerRightCutoff η b δ ρ N (L θ) :=
    funext (actualUpperRightCutoff_reflection η b δ ρ N)
  have hanchor (a : Fin N) : actualUpperAnchorCutoff η b δ ρ a =
      fun θ => actualLowerAnchorCutoff η b δ ρ a (L θ) :=
    funext (actualUpperAnchorCutoff_reflection η b δ ρ a)
  rw [hright]
  exact ⟨(hbound N hN).1.comp_clm L hL,
    fun a => by rw [hanchor]; exact ((hbound N hN).2 a).comp_clm L hL⟩

theorem rightCutoffAnchor_toroidal {N : ℕ} (b δ ρ : ℝ) (a : Fin N)
    (k : Fin N → ℤ) (θ : Fin N → ℝ) :
    rightCutoffAnchor b δ ρ a (toroidalTranslation k θ) = rightCutoffAnchor b δ ρ a θ := by
  have h (i : Fin N) : periodicRightCutoff b δ ρ (toroidalTranslation k θ i) =
      periodicRightCutoff b δ ρ (θ i) :=
    (periodicRightCutoff_periodic b δ ρ).int_mul (k i) (θ i)
  simp only [rightCutoffAnchor, h]

theorem actualLowerRightCutoff_toroidal {N : ℕ} (η b δ ρ : ℝ)
    (k : Fin N → ℤ) (θ : Fin N → ℝ) :
    actualLowerRightCutoff η b δ ρ N (toroidalTranslation k θ) = actualLowerRightCutoff η b δ ρ N θ := by
  rw [actualLowerRightCutoff, actualLowerRightCutoff, lowerPopulationCutoff_toroidal,
    rightCutoffProduct_toroidal]

theorem actualLowerAnchorCutoff_toroidal {N : ℕ} (η b δ ρ : ℝ) (a : Fin N)
    (k : Fin N → ℤ) (θ : Fin N → ℝ) :
    actualLowerAnchorCutoff η b δ ρ a (toroidalTranslation k θ) = actualLowerAnchorCutoff η b δ ρ a θ := by
  rw [actualLowerAnchorCutoff, actualLowerAnchorCutoff, lowerPopulationCutoff_toroidal,
    rightCutoffAnchor_toroidal]

theorem actualWeightedParticleIntegral_constraint_period {n : ℕ} (η τ ξ : ℝ) (s σ : ℂ)
    (g : (Fin (n + 1) → ℝ) → ℂ) (hg : ∀ k θ, g (toroidalTranslation k θ) = g θ)
    (a : ℝ) (l : ℤ) :
    actualWeightedParticleIntegral η τ ξ σ g (2 * Real.pi * l + a) s =
      actualWeightedParticleIntegral η τ ξ σ g a s := by
  unfold actualWeightedParticleIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  rw [affineConstraintAngles_last_period, hg, homotopyPulledDensity_toroidal η τ ξ _
    (isotropicBarePhysicalDensity_periodic s σ)]

theorem actualWeightedParticleIntegral_physical_reflection {n : ℕ} (η τ ξ : ℝ) (s σ : ℂ)
    (g : (Fin (n + 1) → ℝ) → ℂ) (hg : ∀ k θ, g (toroidalTranslation k θ) = g θ)
    (a : ℝ) (ha : a = 0 ∨ a = Real.pi) :
    actualWeightedParticleIntegral η τ ξ σ (fun θ => g (fun i => -θ i)) a s =
      actualWeightedParticleIntegral η τ ξ σ g a s := by
  rw [actualWeightedParticleIntegral_reflection η τ ξ s σ g hg a]
  rcases ha with rfl | rfl
  · rw [neg_zero]
  · have hh := actualWeightedParticleIntegral_constraint_period η τ ξ s σ g hg Real.pi (-1)
    convert hh using 1
    congr 1
    norm_num
    ring

theorem actual_upper_right_anchor_integral_reflection {n : ℕ} (η τ ξ b δ ρ : ℝ)
    (s σ : ℂ) (a : ℝ) :
    actualWeightedParticleIntegral η τ ξ σ (actualUpperRightCutoff η b δ ρ (n + 1)) a s =
      actualWeightedParticleIntegral η τ ξ σ (actualLowerRightCutoff η b δ ρ (n + 1)) (-a) s ∧
      ∀ i : Fin (n + 1),
        actualWeightedParticleIntegral η τ ξ σ (actualUpperAnchorCutoff η b δ ρ i) a s =
          actualWeightedParticleIntegral η τ ξ σ (actualLowerAnchorCutoff η b δ ρ i) (-a) s := by
  constructor
  · rw [show actualUpperRightCutoff η b δ ρ (n + 1) =
        fun θ => actualLowerRightCutoff η b δ ρ (n + 1) (fun i => -θ i) by
      funext θ; exact actualUpperRightCutoff_reflection η b δ ρ (n + 1) θ]
    exact actualWeightedParticleIntegral_reflection η τ ξ s σ _
      (actualLowerRightCutoff_toroidal η b δ ρ) a
  · intro i
    rw [show actualUpperAnchorCutoff η b δ ρ i =
        fun θ => actualLowerAnchorCutoff η b δ ρ i (fun j => -θ j) by
      funext θ; exact actualUpperAnchorCutoff_reflection η b δ ρ i θ]
    exact actualWeightedParticleIntegral_reflection η τ ξ s σ _
      (actualLowerAnchorCutoff_toroidal η b δ ρ i) a

theorem actual_upper_compact_right_integral_reflection {n : ℕ} (η τ ξ b δ ρ : ℝ)
    (s σ : ℂ) (a : ℝ) :
    (∫ x : Fin n → ℝ, actualUpperCompactRightCutoff η b δ ρ (n + 1) (centeredConstraintAngles a x) *
      homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ) (ξ, centeredConstraintAngles a x)) =
      ∫ x : Fin n → ℝ, actualLowerCompactRightCutoff η b δ ρ (n + 1) (centeredConstraintAngles (-a) x) *
        homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ)
          (ξ, centeredConstraintAngles (-a) x) := by
  simp_rw [actualUpperCompactRightCutoff_reflection]
  exact actual_compact_physical_integral_reflection η τ ξ s σ _ a

end IsingBulk.AnisoF002.Isotropic
