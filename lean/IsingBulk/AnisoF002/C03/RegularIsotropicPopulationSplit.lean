import IsingBulk.AnisoF002.C03.RegularIsotropicMixedKernel

/-!
# The exact smooth population partition after the full homotopy

The populations here are the raw sums of the constructed bumps. They
are never divided by N in the cutoff. All three terms are present and
their sum is exactly one on every actual angular tuple.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open scoped Topology BigOperators

def populationTransition (x : ℝ) : ℝ := Real.smoothTransition (4 * x - 1)

theorem populationTransition_bounds (x : ℝ) :
    0 ≤ populationTransition x ∧ populationTransition x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem populationTransition_zero {x : ℝ} (hx : x ≤ 1 / 4) :
    populationTransition x = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)

theorem populationTransition_one {x : ℝ} (hx : 1 / 2 ≤ x) :
    populationTransition x = 1 := Real.smoothTransition.one_of_one_le (by linarith)

theorem populationTransition_contDiff {j : ℕ∞} : ContDiff ℝ j populationTransition :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

def mixedPopulationCutoff {N : ℕ} (η : ℝ) (θ : Fin N → ℝ) : ℝ :=
  populationTransition (actualUpperPopulation η θ) *
    populationTransition (actualLowerPopulation η θ)

def lowerPopulationCutoff {N : ℕ} (η : ℝ) (θ : Fin N → ℝ) : ℝ :=
  (1 - populationTransition (actualUpperPopulation η θ)) *
    (1 + populationTransition (actualLowerPopulation η θ)) / 2

def upperPopulationCutoff {N : ℕ} (η : ℝ) (θ : Fin N → ℝ) : ℝ :=
  (1 - populationTransition (actualLowerPopulation η θ)) *
    (1 + populationTransition (actualUpperPopulation η θ)) / 2

theorem actual_population_partition {N : ℕ} (η : ℝ) (θ : Fin N → ℝ) :
    mixedPopulationCutoff η θ + lowerPopulationCutoff η θ + upperPopulationCutoff η θ = 1 := by
  unfold mixedPopulationCutoff lowerPopulationCutoff upperPopulationCutoff
  ring

theorem actual_population_partition_bounds {N : ℕ} (η : ℝ) (θ : Fin N → ℝ) :
    (0 ≤ mixedPopulationCutoff η θ ∧ mixedPopulationCutoff η θ ≤ 1) ∧
      (0 ≤ lowerPopulationCutoff η θ ∧ lowerPopulationCutoff η θ ≤ 1) ∧
      (0 ≤ upperPopulationCutoff η θ ∧ upperPopulationCutoff η θ ≤ 1) := by
  have hp := populationTransition_bounds (actualUpperPopulation η θ)
  have hq := populationTransition_bounds (actualLowerPopulation η θ)
  have hpq := mul_nonneg hp.1 hq.1
  have hpq' := mul_le_mul hp.2 hq.2 hq.1 zero_le_one
  have hL := mul_nonneg (sub_nonneg.mpr hp.2) (by linarith [hq.1] : 0 ≤
    1 + populationTransition (actualLowerPopulation η θ))
  have hU := mul_nonneg (sub_nonneg.mpr hq.2) (by linarith [hp.1] : 0 ≤
    1 + populationTransition (actualUpperPopulation η θ))
  dsimp [mixedPopulationCutoff, lowerPopulationCutoff, upperPopulationCutoff]
  constructor
  · constructor <;> nlinarith
  constructor <;> constructor <;> nlinarith

theorem mixedPopulationCutoff_support {N : ℕ} (η : ℝ) (θ : Fin N → ℝ)
    (h : mixedPopulationCutoff η θ ≠ 0) :
    1 / 4 < actualUpperPopulation η θ ∧ 1 / 4 < actualLowerPopulation η θ := by
  have hpq := mul_ne_zero_iff.mp h
  constructor
  · by_contra hp
    exact hpq.1 (populationTransition_zero (le_of_not_gt hp))
  · by_contra hq
    exact hpq.2 (populationTransition_zero (le_of_not_gt hq))

theorem lowerPopulationCutoff_support {N : ℕ} (η : ℝ) (θ : Fin N → ℝ)
    (h : lowerPopulationCutoff η θ ≠ 0) : actualUpperPopulation η θ < 1 / 2 := by
  by_contra hp
  have he := populationTransition_one (le_of_not_gt hp)
  exact h (by simp only [lowerPopulationCutoff, he, sub_self, zero_mul, zero_div])

theorem upperPopulationCutoff_support {N : ℕ} (η : ℝ) (θ : Fin N → ℝ)
    (h : upperPopulationCutoff η θ ≠ 0) : actualLowerPopulation η θ < 1 / 2 := by
  by_contra hq
  have he := populationTransition_one (le_of_not_gt hq)
  exact h (by simp only [upperPopulationCutoff, he, sub_self, zero_mul, zero_div])

theorem actualPopulation_reflection {N : ℕ} (η : ℝ) (θ : Fin N → ℝ) :
    actualUpperPopulation η (fun i => -θ i) = actualLowerPopulation η θ ∧
      actualLowerPopulation η (fun i => -θ i) = actualUpperPopulation η θ := by
  constructor
  · rfl
  · simp only [actualLowerPopulation, actualUpperPopulation, lowerPeriodicBump, neg_neg]

theorem actual_population_partition_reflection {N : ℕ} (η : ℝ) (θ : Fin N → ℝ) :
    mixedPopulationCutoff η (fun i => -θ i) = mixedPopulationCutoff η θ ∧
      lowerPopulationCutoff η (fun i => -θ i) = upperPopulationCutoff η θ ∧
      upperPopulationCutoff η (fun i => -θ i) = lowerPopulationCutoff η θ := by
  simp only [mixedPopulationCutoff, lowerPopulationCutoff, upperPopulationCutoff,
    (actualPopulation_reflection η θ).1, (actualPopulation_reflection η θ).2]
  exact ⟨mul_comm _ _, trivial, trivial⟩

theorem actual_mixed_support_kernel_bound {N : ℕ} (hN : 0 < N)
    (S : ℂ) (hSi : 0 < S.im) (hSn : ‖S‖ ≤ 3) {η τ : ℝ}
    (hη : 0 < η) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (θ : Fin N → ℝ)
    (hcut : mixedPopulationCutoff η θ ≠ 0) {σ : ℂ} (hσ : ‖σ‖ ≤ 1) :
    1 - σ * actualBalancedRootProduct S η τ θ ≠ 0 ∧
      ‖(1 + σ * actualBalancedRootProduct S η τ θ) /
        (1 - σ * actualBalancedRootProduct S η τ θ)‖ ≤
        (2 * (1 + mixedRootAttenuationConstant * η * τ / 8) /
          (mixedRootAttenuationConstant * η * τ / 8)) * N :=
  actual_mixed_product_kernel_bound hN S hSi hSn hη hτ hτ1 θ
    (mixedPopulationCutoff_support η θ hcut).1.le
    (mixedPopulationCutoff_support η θ hcut).2.le hσ

end
end IsingBulk.AnisoF002.Isotropic
