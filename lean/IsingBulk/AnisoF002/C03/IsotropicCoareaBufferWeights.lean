import IsingBulk.AnisoF002.C03.IsotropicUniformBumpWindow
import IsingBulk.AnisoF002.C03.IsotropicActualExtremeWeights
import IsingBulk.AnisoF002.C03.IsotropicActualJacobianWeights

/-!
# Genuine phase and Jacobian envelopes with geometry before η

The fixed branch plateau is determined by sin b. No angular support is
chosen after the bump width; all whole-arc constants retain both full
population fractions and every actual Jacobian factor.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Metric

theorem exists_fixedOccupancy_positive_phase_weight_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b → ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ρ υ : ℝ,
        τ ∈ Icc 0 δ → ρ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
      ∀ θ ∈ Icc (-b) δ,
        ‖physicalPhaseAngleSlope (isotropicRadialParameter α ε) (fixedOccupancyAngle η τ ρ υ θ)‖ ≤
          C / Real.sqrt (θ + b + ε + τ * ρ) := by
  obtain ⟨RB, cB, _, hRB, _, hcB, _, hbranch⟩ :=
    exists_isotropic_branch_sine_bounds α b hα hb hpoint
  have hsinb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  let R := min RB (Real.sin b / 4)
  have hR : 0 < R := lt_min hRB (by positivity)
  have hRsin : R ≤ Real.sin b / 2 := (min_le_right _ _).trans (by linarith only [hsinb])
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  rw [Real.cos_pi] at hcos
  have hS : 0 < 2 * Real.cos α := by linarith only [hcos, hpoint]
  obtain ⟨δA, A, hδA, _, hA, haway⟩ := exists_fixedOccupancy_away_phase_bound
    (2 * Real.cos α) b R hS ⟨hb.1.le, hb.2.le⟩ hpoint hR
  let δ := min 1 (min RB (δA / 4))
  let C := max (Real.exp 1 / cB) (Real.exp 1 * A * Real.sqrt (Real.pi + 3))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδB : δ ≤ RB := (min_le_right _ _).trans (min_le_left _ _)
  have hδA4 : δ ≤ δA / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hδAle : δ ≤ δA := by linarith only [hδA4, hδA]
  refine ⟨δ, C, hδ, hδ1, (div_pos (Real.exp_pos 1) hcB).trans_le (le_max_left _ _), ?_⟩
  intro η hη hwidth ε hε hεδ τ ρ υ hτ hρ hυ θ hθ
  let u := θ + b
  let F := u + ε + τ * ρ
  have hu : 0 ≤ u := by dsimp [u]; linarith only [hθ.1]
  have hτρ : 0 ≤ τ * ρ := mul_nonneg hτ.1 hρ.1
  have hτρle : τ * ρ ≤ δ :=
    (show τ * ρ ≤ τ by nlinarith only [hρ.2, hτ.1]).trans hτ.2
  have hF : 0 < F := by dsimp [F]; linarith only [hu, hε, hτρ]
  have hsF : 0 < Real.sqrt F := Real.sqrt_pos.mpr hF
  have hsin : ‖Complex.sin (fixedOccupancyAngle η τ ρ υ θ)‖ ≤ Real.exp 1 := by
    apply (complex_sin_contour_norm_le_abs θ _).trans
    apply Real.exp_le_exp.mpr
    exact (fixedOccupancyShift_abs_le η τ ρ υ θ hτ.1 hρ hυ).trans (hτ.2.trans hδ1)
  by_cases hlocal : u ≤ R
  · have huabs : |u| ≤ RB := by rw [abs_of_nonneg hu]; exact hlocal.trans (min_le_left _ _)
    have hangle : fixedOccupancyAngle η τ ρ υ θ =
        ((-b + u : ℝ) : ℂ) - Complex.I * ((τ * ρ : ℝ) : ℂ) := by
      have hh := fixedOccupancyAngle_geometric_branch b η τ ρ υ u hη hwidth
        (by rw [abs_of_nonneg hu]; exact hlocal.trans hRsin)
      simpa only [u, show -b + (θ + b) = θ by ring] using hh
    have hlo := (hbranch ε hε (hεδ.trans hδB) u (τ * ρ) huabs ⟨hτρ, hτρle.trans hδB⟩).1
    rw [abs_of_nonneg hu] at hlo
    have hden : cB * Real.sqrt F ≤ ‖Complex.sin (upperPhysicalPhase
        (isotropicDispersion (isotropicRadialParameter α ε, fixedOccupancyAngle η τ ρ υ θ)))‖ := by
      rw [hangle]
      exact hlo
    rw [physicalPhaseAngleSlope, norm_div, norm_neg]
    calc
      _ ≤ Real.exp 1 / (cB * Real.sqrt F) :=
        div_le_div₀ (Real.exp_pos 1).le hsin (mul_pos hcB hsF) hden
      _ = (Real.exp 1 / cB) / Real.sqrt F := by ring
      _ ≤ C / Real.sqrt F := div_le_div_of_nonneg_right (le_max_left _ _) hsF.le
  · have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)
    have hsnear : dist (isotropicRadialParameter α ε) ((2 * Real.cos α : ℝ) : ℂ) ≤ δA :=
      hrad.2.2.2.2.trans (by linarith only [hεδ, hδA4])
    have hθA : θ ∈ Icc (-Real.pi - δA) δA :=
      ⟨by linarith only [hθ.1, hb.2, hδA], hθ.2.trans hδAle⟩
    have hfar : R ≤ |θ + b| := by rw [abs_of_nonneg hu]; exact (lt_of_not_ge hlocal).le
    have hp := haway _ hsnear η τ ρ υ θ ⟨hτ.1, hτ.2.trans hδAle⟩ hρ hυ hθA hfar
    have hn : ‖physicalPhaseAngleSlope (isotropicRadialParameter α ε) (fixedOccupancyAngle η τ ρ υ θ)‖ ≤
        Real.exp 1 * A := by
      rw [physicalPhaseAngleSlope, norm_div, norm_neg, div_eq_mul_inv]
      exact mul_le_mul hsin hp (inv_nonneg.mpr (norm_nonneg _)) (Real.exp_pos 1).le
    have hFbound : F ≤ Real.pi + 3 := by
      dsimp [F, u]
      linarith only [hθ.2, hb.2, hεδ, hτρle, hδ1]
    apply hn.trans
    apply (le_div_iff₀ hsF).mpr
    exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hFbound)
      (mul_nonneg (Real.exp_pos 1).le hA.le)).trans (le_max_right _ _)

theorem exists_actual_positive_phase_minimum_envelope_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b → ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b) δ) →
      ∀ m : ℝ, 0 ≤ m → (∀ i, m ≤ θ i + b) → ∀ i : Fin N,
        ‖actualPhaseSlope (isotropicRadialParameter α ε) η τ ξ θ i‖ ≤
          C / Real.sqrt (m + ε + (ξ * τ) * actualUpperOccupancy η θ) := by
  obtain ⟨δ, C, hδ, hδ1, hC, hweight⟩ :=
    exists_fixedOccupancy_positive_phase_weight_buffer α b hα hb hpoint
  refine ⟨δ, C, hδ, hδ1, hC, ?_⟩
  intro η hη hwidth N hN ε hε hεδ τ ξ hτ hξ θ hθ m hm hmin i
  have hτξ : ξ * τ ∈ Icc 0 δ := by
    refine ⟨mul_nonneg hξ.1 hτ.1, ?_⟩
    exact (show ξ * τ ≤ τ by nlinarith only [hξ.2, hτ.1]).trans hτ.2
  have hρ := actualUpperOccupancy_mem_Icc hN η θ
  have hυ := actualLowerOccupancy_mem_Icc hN η θ
  have hh := hweight η hη hwidth ε hε hεδ (ξ * τ) (actualUpperOccupancy η θ) (actualLowerOccupancy η θ)
    hτξ hρ hυ (θ i) (hθ i)
  rw [actualPhaseSlope, actualHomotopyAngle_eq_fixedOccupancy]
  apply hh.trans
  apply div_le_div_of_nonneg_left hC.le
  · apply Real.sqrt_pos.mpr
    have hp := mul_nonneg hτξ.1 hρ.1
    linarith only [hm, hε, hp]
  · exact Real.sqrt_le_sqrt (by linarith only [hmin i])

theorem exists_actual_positive_jacobian_weight_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b → ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ k, θ k ∈ Icc (-b) δ) → ∀ i : Fin N,
        ‖1 + actualPhaseSlope (isotropicRadialParameter α ε) η τ ξ θ i‖ ≤
          C / Real.sqrt (θ i + b + ε + (ξ * τ) * actualUpperOccupancy η θ) := by
  obtain ⟨δ, A, hδ, hδ1, hA, hphase⟩ :=
    exists_fixedOccupancy_positive_phase_weight_buffer α b hα hb hpoint
  refine ⟨δ, Real.sqrt (Real.pi + 3) + A, hδ, hδ1, by positivity, ?_⟩
  intro η hη hwidth N hN ε hε hεδ τ ξ hτ hξ θ hθ i
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
  have hslope := hphase η hη hwidth ε hε hεδ (ξ * τ) (actualUpperOccupancy η θ) (actualLowerOccupancy η θ)
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

theorem exists_actual_whole_arc_jacobian_weight_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ k, θ k ∈ Icc (-Real.pi - δ) δ) →
      ∀ i : Fin N,
        ‖1 + actualPhaseSlope (isotropicRadialParameter α ε) η τ ξ θ i‖ ≤
          C / Real.sqrt (|θ i + b| + ε) := by
  obtain ⟨δ, hδ, hδ1, hdata⟩ := exists_whole_arc_derivative_buffer α b hα hb hpoint
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro η hη hwidth
  obtain ⟨C, hC, hbound⟩ := hdata η hη hwidth
  refine ⟨C, hC, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ hθ i
  have hξτ : ξ * τ ∈ Icc 0 δ := by
    refine ⟨mul_nonneg hξ.1 hτ.1, ?_⟩
    have hh : ξ * τ ≤ τ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hξ.2 hτ.1
    exact hh.trans hτ.2
  have hh := (hbound ε hε hεδ (ξ * τ) (actualUpperOccupancy η θ) (actualLowerOccupancy η θ)
    hξτ (actualUpperOccupancy_mem_Icc hN η θ) (actualLowerOccupancy_mem_Icc hN η θ) (θ i) (hθ i)).2
  rw [actualPhaseSlope, actualHomotopyAngle_eq_fixedOccupancy]
  exact (fixedOccupancy_jacobian_norm_le_regularSlope _ _ _ _ _ _).trans hh

end IsingBulk.AnisoF002.Isotropic
