import IsingBulk.AnisoF002.C03.IsotropicPositivePhaseWeight
import IsingBulk.AnisoF002.C03.IsotropicActualPopulationScales

/-!
# The actual Jacobian weights and occupancy-sensitive extreme scale

The exact alternative between a zero upper population and an actual
positive angular coordinate removes the population depth from the final
extreme-coordinate scale. No generic-ratio or positive-population lower
bound is used.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem actual_extreme_population_depth_comparison {N : ℕ} (hN : 0 < N)
    (b η ε τ ξ : ℝ) (hb : 0 < b) (hη : 0 < η) (hε : 0 < ε)
    (hτ : τ ∈ Icc 0 1) (hξ : ξ ∈ Icc 0 1)
    (θ : Fin N → ℝ) (hθ : ∀ k, -Real.pi ≤ θ k)
    (j : Fin N) (hmax : ∀ k, θ k ≤ θ j) (hM : 0 ≤ θ j + b) :
    θ j + b + ε + (ξ * τ) * actualUpperOccupancy η θ ≤
      (1 + 1 / b) * (θ j + b + ε) := by
  have hρ := actualUpperOccupancy_mem_Icc hN η θ
  have hτξ : 0 ≤ ξ * τ := mul_nonneg hξ.1 hτ.1
  have hτξ1 : ξ * τ ≤ 1 :=
    (show ξ * τ ≤ τ by nlinarith only [hξ.2, hτ.1]).trans hτ.2
  by_cases hzero : actualUpperOccupancy η θ = 0
  · rw [hzero, mul_zero, add_zero]
    have hp : 0 ≤ (1 / b) * (θ j + b + ε) := mul_nonneg (by positivity) (by linarith only [hM, hε])
    nlinarith only [hp]
  · have hpos : 0 < actualUpperOccupancy η θ := lt_of_le_of_ne hρ.1 (Ne.symm hzero)
    obtain ⟨k, hk⟩ := exists_positive_angle_of_upperPopulation_pos η hη θ hθ hpos
    have hMj : b ≤ θ j + b := by linarith only [hk, hmax k]
    have hp : (ξ * τ) * actualUpperOccupancy η θ ≤ 1 :=
      ((mul_le_mul_of_nonneg_left hρ.2 hτξ).trans_eq (mul_one _)).trans hτξ1
    have hone : 1 ≤ (θ j + b + ε) / b := (le_div_iff₀ hb).mpr (by linarith only [hMj, hε])
    have he : (1 + 1 / b) * (θ j + b + ε) = θ j + b + ε + (θ j + b + ε) / b := by ring
    rw [he]
    linarith only [hp, hone]

theorem exists_actual_positive_jacobian_weight (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ k, θ k ∈ Icc (-b) δ) → ∀ i : Fin N,
        ‖1 + actualPhaseSlope (isotropicRadialParameter α ε) η τ ξ θ i‖ ≤
          C / Real.sqrt (θ i + b + ε + (ξ * τ) * actualUpperOccupancy η θ) := by
  obtain ⟨δ, A, hδ, hδ1, hA, hphase⟩ :=
    exists_fixedOccupancy_positive_phase_weight α b η hα hb hpoint hη hwidth
  refine ⟨δ, Real.sqrt (Real.pi + 3) + A, hδ, hδ1, by positivity, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ hθ i
  have hρ := actualUpperOccupancy_mem_Icc hN η θ
  have hυ := actualLowerOccupancy_mem_Icc hN η θ
  have hτξ : 0 ≤ ξ * τ := mul_nonneg hξ.1 hτ.1
  have hτξle : ξ * τ ≤ δ :=
    (show ξ * τ ≤ τ by nlinarith only [hξ.2, hτ.1]).trans hτ.2
  have hdepth : (ξ * τ) * actualUpperOccupancy η θ ≤ δ :=
    ((mul_le_mul_of_nonneg_left hρ.2 hτξ).trans_eq (mul_one _)).trans hτξle
  let F := θ i + b + ε + (ξ * τ) * actualUpperOccupancy η θ
  have hF : 0 < F := by
    have hp := mul_nonneg hτξ hρ.1
    dsimp [F]
    linarith only [(hθ i).1, hε, hp]
  have hsF : 0 < Real.sqrt F := Real.sqrt_pos.mpr hF
  have hFupper : F ≤ Real.pi + 3 := by
    dsimp [F]
    linarith only [(hθ i).2, hb.2, hεδ, hdepth, hδ1]
  have hslope := hphase ε hε hεδ (ξ * τ) (actualUpperOccupancy η θ) (actualLowerOccupancy η θ)
    ⟨hτξ, hτξle⟩ hρ hυ (θ i) (hθ i)
  have hactual : ‖actualPhaseSlope (isotropicRadialParameter α ε) η τ ξ θ i‖ ≤ A / Real.sqrt F := by
    rw [actualPhaseSlope, actualHomotopyAngle_eq_fixedOccupancy]
    exact hslope
  calc
    _ ≤ 1 + ‖actualPhaseSlope (isotropicRadialParameter α ε) η τ ξ θ i‖ := by
      simpa only [norm_one] using norm_add_le (1 : ℂ) (actualPhaseSlope (isotropicRadialParameter α ε) η τ ξ θ i)
    _ ≤ 1 + A / Real.sqrt F := add_le_add le_rfl hactual
    _ = (Real.sqrt F + A) / Real.sqrt F := by field_simp
    _ ≤ (Real.sqrt (Real.pi + 3) + A) / Real.sqrt F :=
      div_le_div_of_nonneg_right (add_le_add (Real.sqrt_le_sqrt hFupper) le_rfl) hsF.le

end IsingBulk.AnisoF002.Isotropic
