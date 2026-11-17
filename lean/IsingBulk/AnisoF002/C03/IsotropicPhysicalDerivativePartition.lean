import IsingBulk.AnisoF002.C03.IsotropicWeightedParticleHolomorphy

/-!
# Every derivative of the complete physical particle partition

The full particle coefficient is defined by its original constrained
angular integral. Its temperature derivatives split into the actual
mixed coefficient, full one-sided right coefficient, and all named
anchors. Holomorphy of every weighted term is proved from physical roots.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter MeasureTheory

def isotropicFullParticleCoefficient (n : ℕ) (a : ℝ) (σ S : ℂ) : ℂ :=
  ∫ x in angularIntegrationBox n,
    isotropicBarePhysicalDensity S σ (fun i => (affineConstraintAngles a x i : ℂ))

theorem isotropicFullParticleCoefficient_analyticAt (n : ℕ) (a : ℝ) (σ S : ℂ)
    (hσ : ‖σ‖ ≤ 1) (hS : 0 < S.im) :
    AnalyticAt ℂ (isotropicFullParticleCoefficient n a σ) S := by
  have he : isotropicFullParticleCoefficient n a σ =
      actualWeightedParticleIntegral (n := n) 1 0 0 σ (fun _ => 1) a := by
    funext T
    simp only [isotropicFullParticleCoefficient, actualWeightedParticleIntegral,
      homotopyPulledDensity_at_zero, one_mul]
  rw [he]
  exact actualWeightedParticleIntegral_analyticAt 1 0 0 σ zero_lt_one le_rfl le_rfl hσ
    _ continuous_const a S hS

theorem exists_actual_complete_particle_derivative_partition (η : ℝ) (hη : 0 < η) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ n : ℕ, ∀ τ ∈ Icc 0 Δ, ∀ b δ ρ a : ℝ,
      a = 0 ∨ a = Real.pi → ∀ σ S : ℂ, ‖σ‖ ≤ 1 → 0 < S.im → ∀ j : ℕ,
      iteratedDeriv j (isotropicFullParticleCoefficient (n + 1) a σ) S =
        iteratedDeriv j (mixedPhysicalCoefficient (n + 1) η τ a σ) S +
        2 * (iteratedDeriv j (actualWeightedParticleIntegral η τ 1 σ
          (actualLowerRightCutoff η b δ ρ (n + 2)) a) S +
          ∑ i : Fin (n + 2), iteratedDeriv j (actualWeightedParticleIntegral η τ 1 σ
            (actualLowerAnchorCutoff η b δ ρ i) a) S) := by
  obtain ⟨Δ, hΔ, hpart⟩ := exists_actual_complete_particle_partition η hη
  refine ⟨Δ, hΔ, ?_⟩
  intro n τ hτ b δ ρ a ha σ S hσ hS j
  let M : ℂ → ℂ := actualWeightedParticleIntegral (n := n + 1) η τ 1 σ
    (fun θ => (mixedPopulationCutoff η θ : ℂ)) a
  let R : ℂ → ℂ := actualWeightedParticleIntegral η τ 1 σ
    (actualLowerRightCutoff η b δ ρ (n + 2)) a
  let A : Fin (n + 2) → ℂ → ℂ := fun i => actualWeightedParticleIntegral η τ 1 σ
    (actualLowerAnchorCutoff η b δ ρ i) a
  have hM : ContDiffAt ℂ j M S := (actualWeightedParticleIntegral_analyticAt η τ 1 σ hη hτ.1
    zero_le_one hσ _ (Complex.continuous_ofReal.comp (mixedPopulationCutoff_continuous η)) a S hS).contDiffAt
  have hR : ContDiffAt ℂ j R S := (actualWeightedParticleIntegral_analyticAt η τ 1 σ hη hτ.1
    zero_le_one hσ _ (actualLowerRightCutoff_contDiff η b δ ρ (n + 2) (k := 0)).continuous a S hS).contDiffAt
  have hA (i : Fin (n + 2)) : ContDiffAt ℂ j (A i) S :=
    (actualWeightedParticleIntegral_analyticAt η τ 1 σ hη hτ.1 zero_le_one hσ _
      (actualLowerAnchorCutoff_contDiff η b δ ρ i (k := 0)).continuous a S hS).contDiffAt
  have hAS : ContDiffAt ℂ j (fun T => ∑ i, A i T) S := ContDiffAt.sum (fun i _ => hA i)
  have he : isotropicFullParticleCoefficient (n + 1) a σ =ᶠ[𝓝 S]
      fun T => M T + 2 * (R T + ∑ i, A i T) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hS] with T hT
    exact hpart n τ hτ T σ hT hσ b δ ρ a ha
  rw [(he.iteratedDeriv j).eq_of_nhds,
    iteratedDeriv_fun_add hM (contDiffAt_const.mul (hR.add hAS)),
    iteratedDeriv_const_mul 2 (hR.add hAS), iteratedDeriv_fun_add hR hAS,
    iteratedDeriv_fun_sum (fun i _ => hA i)]
  have hme : M = mixedPhysicalCoefficient (n + 1) η τ a σ :=
    funext (fun T => (mixedPhysicalCoefficient_eq_weightedIntegral (n + 1) η τ a σ T).symm)
  rw [hme]

end IsingBulk.AnisoF002.Isotropic
