import IsingBulk.AnisoF002.C03.IsotropicOccupancyCorrection
import IsingBulk.AnisoF002.C03.IsotropicPositivePhaseWeight

/-!
# The full population correction at the actual curvature scale

The physical phase-slope envelope is inserted into the exact differentiated
population formula. The resulting bound is uniform before particle number
and carries the same extreme-coordinate curvature scale as the coarea
denominator. No positive lower bound on either population is imposed.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def positiveCurvatureScale (m M E : ℝ) : ℝ :=
  2 * (M - m) / (Real.sqrt (m + E) * Real.sqrt (M + E) *
    (Real.sqrt (m + E) + Real.sqrt (M + E)))

theorem positiveCurvatureScale_nonneg {m M E : ℝ} (hm : 0 ≤ m)
    (hM : m ≤ M) (hE : 0 < E) : 0 ≤ positiveCurvatureScale m M E := by
  unfold positiveCurvatureScale
  positivity

theorem positiveCurvatureScale_pos {m M E : ℝ} (hm : 0 ≤ m)
    (hM : m < M) (hE : 0 < E) : 0 < positiveCurvatureScale m M E := by
  have hgap : 0 < M - m := sub_pos.mpr hM
  have hME : 0 < M + E := by linarith only [hm, hM, hE]
  unfold positiveCurvatureScale
  positivity

theorem angular_gap_div_sqrt_curvature {m M E H : ℝ} (hm : 0 ≤ m)
    (hM : m ≤ M) (hE : 0 < E) (hH : M + E ≤ H) :
    (M - m) / Real.sqrt (m + E) ≤ H * positiveCurvatureScale m M E := by
  have ha : 0 < Real.sqrt (m + E) := Real.sqrt_pos.mpr (by linarith only [hm, hE])
  have hb : 0 < Real.sqrt (M + E) := Real.sqrt_pos.mpr (by linarith only [hm, hM, hE])
  have hab : Real.sqrt (m + E) ≤ Real.sqrt (M + E) := Real.sqrt_le_sqrt (by linarith only [hM])
  have hsum : Real.sqrt (m + E) + Real.sqrt (M + E) ≠ 0 := by positivity
  have he : (M - m) / Real.sqrt (m + E) =
      (Real.sqrt (M + E) * (Real.sqrt (m + E) + Real.sqrt (M + E)) / 2) *
        positiveCurvatureScale m M E := by
    unfold positiveCurvatureScale
    field_simp
  rw [he]
  apply mul_le_mul_of_nonneg_right _ (positiveCurvatureScale_nonneg hm hM hE)
  have hprod := mul_le_mul_of_nonneg_left hab hb.le
  have hsq := Real.sq_sqrt (show 0 ≤ M + E by linarith only [hm, hM, hE])
  nlinarith only [hprod, hsq, hH]

/-- Both full population derivatives cost only tau times the actual
curvature scale. The neighborhood and constant precede all N and every
population fraction, including zero populations. -/
theorem exists_actual_occupancy_correction_curvature_bound (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ k, θ k ∈ Icc (-b) δ) →
      ∀ i j : Fin N, (∀ k, θ i ≤ θ k) → (∀ k, θ k ≤ θ j) →
        ‖actualOccupancyPhaseCorrection (isotropicRadialParameter α ε) η τ ξ θ i -
            actualOccupancyPhaseCorrection (isotropicRadialParameter α ε) η τ ξ θ j‖ ≤
          (ξ * τ) * C * positiveCurvatureScale (θ i + b) (θ j + b)
            (ε + (ξ * τ) * actualUpperOccupancy η θ) := by
  obtain ⟨δ, A, hδ, hδ1, hA, hphase⟩ :=
    exists_actual_positive_phase_minimum_envelope α b η hα hb hpoint hη hwidth
  obtain ⟨L, hL, hcorr⟩ := exists_actual_occupancy_correction_difference_bound η
  refine ⟨δ, L * A * (Real.pi + 3), hδ, hδ1, by positivity, ?_⟩
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
      hphase N hN ε hε hεδ τ ξ hτ hξ θ hθ m hm (by intro l; dsimp [m]; linarith only [hmin l]) k
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
