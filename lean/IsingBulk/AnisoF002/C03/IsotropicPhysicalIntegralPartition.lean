import IsingBulk.AnisoF002.C03.IsotropicUpperReflectionJets

/-!
# Exact full physical population and compact-anchor integral partition

All terms are the actual complete normalized density on the original
independent angular box. Integrability is proved from its upper-sheet
analyticity. The reflected upper sector equals the lower sector at
the two physical constraints; every named anchor is retained.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory

theorem actual_physical_density_continuous {N : ℕ} (hN : 0 < N) (s σ : ℂ)
    (hs : 0 < s.im) (hσ : ‖σ‖ ≤ 1) (η τ ξ : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) :
    Continuous (fun θ : Fin N → ℝ =>
      homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ) (ξ, θ)) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  exact (homotopyPulledDensity_contDiffAt η τ (isotropicBarePhysicalDensity s σ) (ξ, θ)
    (isotropicBarePhysicalDensity_analyticAt hN s σ hσ _
      (fun i => actual_balanced_homotopy_sheet s hs η τ ξ hη hτ hξ θ i))).continuousAt.comp
        (continuous_const.prodMk continuous_id).continuousAt

theorem actual_weighted_particle_integrable {n : ℕ} (s σ : ℂ)
    (hs : 0 < s.im) (hσ : ‖σ‖ ≤ 1) (η τ ξ : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (g : (Fin (n + 1) → ℝ) → ℂ) (hg : Continuous g) (a : ℝ) :
    IntegrableOn (fun x : Fin n → ℝ => g (affineConstraintAngles a x) *
      homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ) (ξ, affineConstraintAngles a x))
      (angularIntegrationBox n) volume := by
  have hD := actual_physical_density_continuous (by omega : 0 < n + 1) s σ hs hσ η τ ξ hη hτ hξ
  have hc := (hg.mul hD).comp (affineConstraintAngles_contDiff a 0).continuous
  exact hc.continuousOn.integrableOn_Icc

theorem mixedPopulationCutoff_continuous_partition (η : ℝ) (N : ℕ) :
    Continuous (@mixedPopulationCutoff N η) :=
  ((populationTransition_contDiff (j := 0)).continuous.comp
    (actualUpperPopulation_contDiff η N (k := 0)).continuous).mul
    ((populationTransition_contDiff (j := 0)).continuous.comp
      (actualLowerPopulation_contDiff η N (k := 0)).continuous)

theorem upperPopulationCutoff_continuous (η : ℝ) (N : ℕ) :
    Continuous (@upperPopulationCutoff N η) := by
  have he : @upperPopulationCutoff N η = fun θ => lowerPopulationCutoff η (-θ) := by
    funext θ
    exact (actual_population_partition_reflection η θ).2.1.symm
  rw [he]
  exact (lowerPopulationCutoff_contDiff η N (k := 0)).continuous.comp continuous_neg

theorem actual_population_integral_partition {n : ℕ} (s σ : ℂ)
    (hs : 0 < s.im) (hσ : ‖σ‖ ≤ 1) (η τ ξ : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (a : ℝ) :
    actualWeightedParticleIntegral (n := n) η τ ξ σ (fun _ => 1) a s =
      actualWeightedParticleIntegral (n := n) η τ ξ σ (fun θ => (mixedPopulationCutoff η θ : ℂ)) a s +
      actualWeightedParticleIntegral (n := n) η τ ξ σ (fun θ => (lowerPopulationCutoff η θ : ℂ)) a s +
      actualWeightedParticleIntegral (n := n) η τ ξ σ (fun θ => (upperPopulationCutoff η θ : ℂ)) a s := by
  have hF := actual_weighted_particle_integrable s σ hs hσ η τ ξ hη hτ hξ
    (fun θ : Fin (n + 1) → ℝ => (mixedPopulationCutoff η θ : ℂ))
    (Complex.continuous_ofReal.comp (mixedPopulationCutoff_continuous_partition η (n + 1))) a
  have hL := actual_weighted_particle_integrable s σ hs hσ η τ ξ hη hτ hξ
    (fun θ : Fin (n + 1) → ℝ => (lowerPopulationCutoff η θ : ℂ))
    (lowerPopulationCutoff_complex_contDiff η (n + 1) (k := 0)).continuous a
  have hU := actual_weighted_particle_integrable s σ hs hσ η τ ξ hη hτ hξ
    (fun θ : Fin (n + 1) → ℝ => (upperPopulationCutoff η θ : ℂ))
    (Complex.continuous_ofReal.comp (upperPopulationCutoff_continuous η (n + 1))) a
  unfold actualWeightedParticleIntegral
  have hadd := integral_add (hF.add hL) hU
  simp only [Pi.add_apply] at hadd
  rw [← integral_add hF hL, ← hadd]
  apply integral_congr_ae
  filter_upwards [] with x
  have hp : (mixedPopulationCutoff η (affineConstraintAngles a x) : ℂ) +
      (lowerPopulationCutoff η (affineConstraintAngles a x) : ℂ) +
      (upperPopulationCutoff η (affineConstraintAngles a x) : ℂ) = 1 := by
    exact_mod_cast actual_population_partition η (affineConstraintAngles a x)
  rw [← add_mul, ← add_mul, hp]

theorem actual_lower_right_anchor_integral_partition {n : ℕ} (s σ : ℂ)
    (hs : 0 < s.im) (hσ : ‖σ‖ ≤ 1) (η τ ξ b δ ρ : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (a : ℝ) :
    actualWeightedParticleIntegral (n := n) η τ ξ σ (fun θ => (lowerPopulationCutoff η θ : ℂ)) a s =
      actualWeightedParticleIntegral η τ ξ σ (actualLowerRightCutoff η b δ ρ (n + 1)) a s +
      ∑ i : Fin (n + 1), actualWeightedParticleIntegral η τ ξ σ (actualLowerAnchorCutoff η b δ ρ i) a s := by
  have hR := actual_weighted_particle_integrable s σ hs hσ η τ ξ hη hτ hξ
    (actualLowerRightCutoff η b δ ρ (n + 1)) (actualLowerRightCutoff_contDiff η b δ ρ (n + 1) (k := 0)).continuous a
  have hA (i : Fin (n + 1)) := actual_weighted_particle_integrable s σ hs hσ η τ ξ hη hτ hξ
    (actualLowerAnchorCutoff η b δ ρ i) (actualLowerAnchorCutoff_contDiff η b δ ρ i (k := 0)).continuous a
  unfold actualWeightedParticleIntegral
  rw [← integral_finsetSum _ (fun i _ => hA i), ← integral_add hR (integrable_finsetSum _ (fun i _ => hA i))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [actual_lower_right_anchor_partition η b δ ρ, add_mul, Finset.sum_mul]

/-- Complete physical integral: every mixed term, twice the full right
term, and twice every named compact-left anchor, on the original box. -/
theorem actual_complete_integral_lower_partition {n : ℕ} (s σ : ℂ)
    (hs : 0 < s.im) (hσ : ‖σ‖ ≤ 1) (η τ ξ b δ ρ : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (a : ℝ) (ha : a = 0 ∨ a = Real.pi) :
    actualWeightedParticleIntegral (n := n) η τ ξ σ (fun _ => 1) a s =
      actualWeightedParticleIntegral (n := n) η τ ξ σ (fun θ => (mixedPopulationCutoff η θ : ℂ)) a s +
      2 * (actualWeightedParticleIntegral η τ ξ σ (actualLowerRightCutoff η b δ ρ (n + 1)) a s +
        ∑ i : Fin (n + 1), actualWeightedParticleIntegral η τ ξ σ (actualLowerAnchorCutoff η b δ ρ i) a s) := by
  rw [actual_population_integral_partition s σ hs hσ η τ ξ hη hτ hξ a,
    actual_upper_population_physical_functions η τ ξ σ a ha,
    actual_lower_right_anchor_integral_partition s σ hs hσ η τ ξ b δ ρ hη hτ hξ a]
  ring

end IsingBulk.AnisoF002.Isotropic
