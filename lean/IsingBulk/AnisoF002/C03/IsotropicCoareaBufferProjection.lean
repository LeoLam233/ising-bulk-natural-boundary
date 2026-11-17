import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferIntegrated
import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferCorrection
import IsingBulk.AnisoF002.C03.IsotropicActualExtremeProjection

/-!
# Actual constrained extreme projection with separate angular and time buffers
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric

theorem exists_actual_extreme_phase_projection_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ c : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < c ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ k, θ k ∈ Icc (-b) β) →
      ∀ i j : Fin N, (∀ k, θ i ≤ θ k) → (∀ k, θ k ≤ θ j) →
        c * positiveCurvatureScale (θ i + b) (θ j + b)
            (ε + (ξ * τ) * actualUpperOccupancy η θ) ≤
          (frozenObliqueRotation *
            (actualFullPhaseDerivative (isotropicRadialParameter α ε) η τ ξ θ i -
              actualFullPhaseDerivative (isotropicRadialParameter α ε) η τ ξ θ j)).re := by
  obtain ⟨βB, hβB, hβB1, hBdata⟩ :=
    exists_fixedOccupancy_phase_slope_difference_buffer α b hα hb hpoint
  obtain ⟨βC, hβC, _, hCdata⟩ :=
    exists_actual_occupancy_correction_curvature_buffer α b hα hb hpoint
  let β := min βB βC
  have hβ : 0 < β := lt_min hβB hβC
  have hβB' : β ≤ βB := min_le_left _ _
  have hβC' : β ≤ βC := min_le_right _ _
  refine ⟨β, hβ, hβB'.trans hβB1, ?_⟩
  intro η hη hwidth
  obtain ⟨δB, cB, hδB, _, hcB, hfixed⟩ := hBdata η hη hwidth
  obtain ⟨C, hC, hcorr⟩ := hCdata η hη hwidth
  let δ := min β (min δB (cB / (2 * C)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδβ : δ ≤ β := min_le_left _ _
  have hδB' : δ ≤ δB := (min_le_right _ _).trans (min_le_left _ _)
  have hδC' : δ ≤ βC := hδβ.trans hβC'
  have hδsmall : δ ≤ cB / (2 * C) := (min_le_right _ _).trans (min_le_right _ _)
  have hδCsmall : δ * C ≤ cB / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp hδsmall
    nlinarith only [hh]
  refine ⟨δ, cB / 2, hδ, hδβ, half_pos hcB, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ hθ i j hmin hmax
  let E := ε + (ξ * τ) * actualUpperOccupancy η θ
  let L := positiveCurvatureScale (θ i + b) (θ j + b) E
  let s := isotropicRadialParameter α ε
  have hρ := actualUpperOccupancy_mem_Icc hN η θ
  have hυ := actualLowerOccupancy_mem_Icc hN η θ
  have hτξ : 0 ≤ ξ * τ := mul_nonneg hξ.1 hτ.1
  have hτξle : ξ * τ ≤ δ :=
    (show ξ * τ ≤ τ by nlinarith only [hξ.2, hτ.1]).trans hτ.2
  have hm : 0 ≤ θ i + b := by linarith only [(hθ i).1]
  have hmM : θ i + b ≤ θ j + b := by linarith only [hmax i]
  have hE : 0 < E := add_pos_of_pos_of_nonneg hε (mul_nonneg hτξ hρ.1)
  have hL : 0 ≤ L := positiveCurvatureScale_nonneg hm hmM hE
  have hfixed' := hfixed ε hε (hεδ.trans hδB') (ξ * τ)
    (actualUpperOccupancy η θ) (actualLowerOccupancy η θ)
    ⟨hτξ, hτξle.trans hδB'⟩ hρ hυ (θ i + b) (θ j + b) hm hmM
    (by linarith only [(hθ j).2, hβB'])
  rw [show -b + (θ i + b) = θ i by ring, show -b + (θ j + b) = θ j by ring] at hfixed'
  change cB * L ≤ _ at hfixed'
  have hcorr' := hcorr N hN ε hε (hεδ.trans hδC') τ ξ
    ⟨hτ.1, hτ.2.trans hδC'⟩ hξ θ
    (fun k => ⟨(hθ k).1, (hθ k).2.trans hβC'⟩) i j hmin hmax
  change ‖actualOccupancyPhaseCorrection s η τ ξ θ i - actualOccupancyPhaseCorrection s η τ ξ θ j‖ ≤
    (ξ * τ) * C * L at hcorr'
  have hcorrSmall : ‖actualOccupancyPhaseCorrection s η τ ξ θ i - actualOccupancyPhaseCorrection s η τ ξ θ j‖ ≤
      (cB / 2) * L := by
    apply hcorr'.trans
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right hτξle hC.le).trans hδCsmall) hL
  have herror := frozen_projection_ge_neg_norm
    (actualOccupancyPhaseCorrection s η τ ξ θ i - actualOccupancyPhaseCorrection s η τ ξ θ j)
  have he : (frozenObliqueRotation * (actualFullPhaseDerivative s η τ ξ θ i - actualFullPhaseDerivative s η τ ξ θ j)).re =
      (frozenObliqueRotation *
        (fixedOccupancyPhaseSlope s η (ξ * τ) (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) (θ i) -
          fixedOccupancyPhaseSlope s η (ξ * τ) (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) (θ j))).re +
      (frozenObliqueRotation *
        (actualOccupancyPhaseCorrection s η τ ξ θ i - actualOccupancyPhaseCorrection s η τ ξ θ j)).re := by
    rw [actualFullPhaseDerivative_fixedSlope, actualFullPhaseDerivative_fixedSlope]
    have hh : ∀ a b c d : ℂ,
        frozenObliqueRotation * ((a + b) - (c + d)) =
          frozenObliqueRotation * (a - c) + frozenObliqueRotation * (b - d) := by intros; ring
    rw [hh, Complex.add_re]
  change (cB / 2) * L ≤ (frozenObliqueRotation * (actualFullPhaseDerivative s η τ ξ θ i - actualFullPhaseDerivative s η τ ξ θ j)).re
  rw [he]
  linarith only [hfixed', herror, hcorrSmall]

end IsingBulk.AnisoF002.Isotropic
