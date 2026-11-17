import IsingBulk.AnisoF002.C03.IsotropicActualOccupancyPhase

/-!
# The full phase-slope envelope on the nonnegative branch side

The denominator includes the actual common outward depth tau rho.
Consequently every full population sum has the same minimum envelope,
which will control the occupancy correction in the coarea direction.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem exists_fixedOccupancy_positive_phase_weight (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ρ υ : ℝ,
        τ ∈ Icc 0 δ → ρ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
      ∀ θ ∈ Icc (-b) δ,
        ‖physicalPhaseAngleSlope (isotropicRadialParameter α ε) (fixedOccupancyAngle η τ ρ υ θ)‖ ≤
          C / Real.sqrt (θ + b + ε + τ * ρ) := by
  obtain ⟨RB, cB, _, hRB, _, hcB, _, hbranch⟩ :=
    exists_isotropic_branch_sine_bounds α b hα hb hpoint
  let R := min RB (η / 2)
  have hR : 0 < R := lt_min hRB (by positivity)
  have hRη : R ≤ η := (min_le_right _ _).trans (by linarith only [hη])
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
  intro ε hε hεδ τ ρ υ hτ hρ hυ θ hθ
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
      have hh := fixedOccupancyAngle_on_branch b η τ ρ υ u hη hwidth
        (by rw [abs_of_nonneg hu]; exact hlocal.trans hRη)
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

theorem exists_actual_positive_phase_minimum_envelope (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b) δ) →
      ∀ m : ℝ, 0 ≤ m → (∀ i, m ≤ θ i + b) → ∀ i : Fin N,
        ‖actualPhaseSlope (isotropicRadialParameter α ε) η τ ξ θ i‖ ≤
          C / Real.sqrt (m + ε + (ξ * τ) * actualUpperOccupancy η θ) := by
  obtain ⟨δ, C, hδ, hδ1, hC, hweight⟩ :=
    exists_fixedOccupancy_positive_phase_weight α b η hα hb hpoint hη hwidth
  refine ⟨δ, C, hδ, hδ1, hC, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ hθ m hm hmin i
  have hτξ : ξ * τ ∈ Icc 0 δ := by
    refine ⟨mul_nonneg hξ.1 hτ.1, ?_⟩
    exact (show ξ * τ ≤ τ by nlinarith only [hξ.2, hτ.1]).trans hτ.2
  have hρ := actualUpperOccupancy_mem_Icc hN η θ
  have hυ := actualLowerOccupancy_mem_Icc hN η θ
  have hh := hweight ε hε hεδ (ξ * τ) (actualUpperOccupancy η θ) (actualLowerOccupancy η θ)
    hτξ hρ hυ (θ i) (hθ i)
  rw [actualPhaseSlope, actualHomotopyAngle_eq_fixedOccupancy]
  apply hh.trans
  apply div_le_div_of_nonneg_left hC.le
  · apply Real.sqrt_pos.mpr
    have hp := mul_nonneg hτξ.1 hρ.1
    linarith only [hm, hε, hp]
  · exact Real.sqrt_le_sqrt (by linarith only [hmin i])

end IsingBulk.AnisoF002.Isotropic
