import IsingBulk.AnisoF002.C03.IsotropicActualExtremeProjection
import IsingBulk.AnisoF002.C03.IsotropicActualExtremeWeights
import IsingBulk.AnisoF002.C03.IsotropicExtremeRatioAlgebra

/-!
# The full physical constrained extreme-coordinate ratio

This is frozen F002 `eq:iso-extreme-ratio` for the actual canonical
phase on the actual balanced contour. The derivative follows the
constraint and includes both full population derivatives. Its positive
oblique projection and the correct Jacobian ratio are proved uniformly
before particle number and all population choices.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem exists_actual_constrained_extreme_ratio (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ k, θ k ∈ Icc (-b) δ) →
      ∀ i j : Fin N, (∀ k, θ i ≤ θ k) → (∀ k, θ k ≤ θ j) → θ i < θ j →
        let s := isotropicRadialParameter α ε
        let D := actualFullPhaseDerivative s η τ ξ θ i - actualFullPhaseDerivative s η τ ξ θ j
        HasDerivAt (fun t : ℝ => actualTotalPhase η τ ξ (s, constrainedAngleLine θ i j t)) D 0 ∧
          0 < (frozenObliqueRotation * D).re ∧
          ‖(1 + actualPhaseSlope s η τ ξ θ i) * (1 + actualPhaseSlope s η τ ξ θ j)‖ /
              (frozenObliqueRotation * D).re ≤
            C * Real.sqrt (θ j + b + ε) / (θ j - θ i) := by
  obtain ⟨δP, c, hδP, hδP1, hc, hprojection⟩ :=
    exists_actual_extreme_phase_projection α b η hα hb hpoint hη hwidth
  obtain ⟨δW, A, hδW, _, hA, hweight⟩ :=
    exists_actual_positive_jacobian_weight α b η hα hb hpoint hη hwidth
  let δ := min δP δW
  let Q := 1 + 1 / b
  let C := (A ^ 2 / c) * Real.sqrt Q
  have hQ : 0 < Q := add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg zero_le_one hb.1.le)
  have hδ : 0 < δ := lt_min hδP hδW
  have hδP' : δ ≤ δP := min_le_left _ _
  have hδW' : δ ≤ δW := min_le_right _ _
  have hδ1 : δ ≤ 1 := hδP'.trans hδP1
  refine ⟨δ, C, hδ, hδ1, by dsimp [C]; positivity, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ hθ i j hmin hmax hij
  let s := isotropicRadialParameter α ε
  let m := θ i + b
  let M := θ j + b
  let E := ε + (ξ * τ) * actualUpperOccupancy η θ
  let D := actualFullPhaseDerivative s η τ ξ θ i - actualFullPhaseDerivative s η τ ξ θ j
  let P := (frozenObliqueRotation * D).re
  let F := ‖(1 + actualPhaseSlope s η τ ξ θ i) * (1 + actualPhaseSlope s η τ ξ θ j)‖
  have hs : 0 < s.im := (isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)).2.2.2.1
  have hρ := actualUpperOccupancy_mem_Icc hN η θ
  have hm : 0 ≤ m := by dsimp [m]; linarith only [(hθ i).1]
  have hmM : m < M := by dsimp [m, M]; linarith only [hij]
  have hM : 0 ≤ M := hm.trans hmM.le
  have hτξ : 0 ≤ ξ * τ := mul_nonneg hξ.1 hτ.1
  have hE : 0 < E := add_pos_of_pos_of_nonneg hε (mul_nonneg hτξ hρ.1)
  have hP : c * positiveCurvatureScale m M E ≤ P :=
    hprojection N hN ε hε (hεδ.trans hδP') τ ξ ⟨hτ.1, hτ.2.trans hδP'⟩ hξ θ
      (fun k => ⟨(hθ k).1, (hθ k).2.trans hδP'⟩) i j hmin hmax
  have hwi := hweight N hN ε hε (hεδ.trans hδW') τ ξ ⟨hτ.1, hτ.2.trans hδW'⟩ hξ θ
    (fun k => ⟨(hθ k).1, (hθ k).2.trans hδW'⟩) i
  have hwj := hweight N hN ε hε (hεδ.trans hδW') τ ξ ⟨hτ.1, hτ.2.trans hδW'⟩ hξ θ
    (fun k => ⟨(hθ k).1, (hθ k).2.trans hδW'⟩) j
  have hwi' : ‖1 + actualPhaseSlope s η τ ξ θ i‖ ≤ A / Real.sqrt (m + E) := by
    simpa only [m, E, add_assoc] using hwi
  have hwj' : ‖1 + actualPhaseSlope s η τ ξ θ j‖ ≤ A / Real.sqrt (M + E) := by
    simpa only [M, E, add_assoc] using hwj
  have hF : F ≤ A ^ 2 / (Real.sqrt (m + E) * Real.sqrt (M + E)) := by
    dsimp [F]
    rw [norm_mul]
    exact (mul_le_mul hwi' hwj' (norm_nonneg _) (by positivity)).trans_eq (by ring)
  obtain ⟨hPpos, hratio⟩ := extreme_jacobian_curvature_ratio hm hmM hE hc hF hP
  have hdepth := actual_extreme_population_depth_comparison hN b η ε τ ξ hb.1 hη hε
    ⟨hτ.1, hτ.2.trans hδ1⟩ hξ θ
      (fun k => by linarith only [(hθ k).1, hb.2]) j hmax hM
  have hscale : M + E ≤ Q * (M + ε) := by simpa only [M, E, Q, add_assoc] using hdepth
  have hroot : Real.sqrt (M + E) ≤ Real.sqrt Q * Real.sqrt (M + ε) := by
    have hh := Real.sqrt_le_sqrt hscale
    rwa [Real.sqrt_mul hQ.le] at hh
  have hratio' : F / P ≤ C * Real.sqrt (M + ε) / (M - m) := by
    apply hratio.trans
    calc
      _ ≤ (A ^ 2 / c) * (Real.sqrt Q * Real.sqrt (M + ε)) / (M - m) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity)) (sub_nonneg.mpr hmM.le)
      _ = _ := by dsimp [C]; ring
  refine ⟨actualTotalPhase_constrainedLine_hasDerivAt s hs η τ ξ hη hτ.1 hξ.1 θ i j, hPpos, ?_⟩
  simpa only [F, P, D, M, m, add_sub_add_right_eq_sub] using hratio'

end IsingBulk.AnisoF002.Isotropic
