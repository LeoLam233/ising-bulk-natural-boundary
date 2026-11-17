import IsingBulk.AnisoF002.C03.IsotropicCoareaBufferWeights
import IsingBulk.AnisoF002.C03.IsotropicCorrectionCurvature

/-!
# Full population correction on the fixed coarea angular buffer
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric

theorem exists_actual_occupancy_correction_curvature_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ k, θ k ∈ Icc (-b) δ) →
      ∀ i j : Fin N, (∀ k, θ i ≤ θ k) → (∀ k, θ k ≤ θ j) →
        ‖actualOccupancyPhaseCorrection (isotropicRadialParameter α ε) η τ ξ θ i -
            actualOccupancyPhaseCorrection (isotropicRadialParameter α ε) η τ ξ θ j‖ ≤
          (ξ * τ) * C * positiveCurvatureScale (θ i + b) (θ j + b)
            (ε + (ξ * τ) * actualUpperOccupancy η θ) := by
  obtain ⟨δ, A, hδ, hδ1, hA, hphase⟩ :=
    exists_actual_positive_phase_minimum_envelope_buffer α b hα hb hpoint
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro η hη hwidth
  obtain ⟨L, hL, hcorr⟩ := exists_actual_occupancy_correction_difference_bound η
  refine ⟨L * A * (Real.pi + 3), by positivity, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ hθ i j hmin hmax
  let E := ε + (ξ * τ) * actualUpperOccupancy η θ
  let m := θ i + b
  let M := θ j + b
  have hρ := actualUpperOccupancy_mem_Icc hN η θ
  have hτξ : 0 ≤ ξ * τ := mul_nonneg hξ.1 hτ.1
  have hτξle : ξ * τ ≤ 1 :=
    (show ξ * τ ≤ τ by nlinarith only [hξ.2, hτ.1]).trans (hτ.2.trans hδ1)
  have hE : 0 < E := by
    dsimp [E]
    exact add_pos_of_pos_of_nonneg hε (mul_nonneg hτξ hρ.1)
  have hm : 0 ≤ m := by dsimp [m]; linarith only [(hθ i).1]
  have hmM : m ≤ M := by dsimp [m, M]; linarith only [hmax i]
  have hF : 0 < m + E := by positivity
  have hQ : 0 ≤ A / Real.sqrt (m + E) := div_nonneg hA.le (Real.sqrt_nonneg _)
  have hψ : ∀ k, ‖actualPhaseSlope (isotropicRadialParameter α ε) η τ ξ θ k‖ ≤
      A / Real.sqrt (m + E) := by
    intro k
    simpa only [m, E, add_assoc] using
      hphase η hη hwidth N hN ε hε hεδ τ ξ hτ hξ θ hθ m hm (by intro l; dsimp [m]; linarith only [hmin l]) k
  have hraw := hcorr N hN (isotropicRadialParameter α ε) τ ξ hτ.1 hξ.1 θ
    (A / Real.sqrt (m + E)) hQ hψ i j
  have hgap : |θ i - θ j| = M - m := by
    rw [abs_of_nonpos (sub_nonpos.mpr (hmax i))]
    dsimp [M, m]
    ring
  rw [hgap] at hraw
  have hbound : M + E ≤ Real.pi + 3 := by
    have hp : (ξ * τ) * actualUpperOccupancy η θ ≤ 1 :=
      (mul_le_mul_of_nonneg_left hρ.2 hτξ).trans (by simpa only [mul_one] using hτξle)
    dsimp [M, E]
    linarith only [(hθ j).2, hb.2, hεδ, hp, hδ1]
  have hscale := angular_gap_div_sqrt_curvature hm hmM hE hbound
  calc
    _ ≤ (ξ * τ) * L * (A / Real.sqrt (m + E)) * (M - m) := hraw
    _ = ((ξ * τ) * L * A) * ((M - m) / Real.sqrt (m + E)) := by ring
    _ ≤ ((ξ * τ) * L * A) * ((Real.pi + 3) * positiveCurvatureScale m M E) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

end IsingBulk.AnisoF002.Isotropic
