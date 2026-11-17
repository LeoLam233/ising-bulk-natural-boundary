import IsingBulk.AnisoF002.C03.IsotropicActualOccupancyPhase

/-!
# Independent Jacobian majorants for every actual angular coordinate

The full real angular rectangle, its endpoint slivers and both sides
of the branch point use one integrable majorant. The full populations
remain in the actual phase. The real part of the fixed-population
contour derivative is exactly one, so removing it only decreases norm.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem fixedOccupancySlope_norm_ge_one (η τ ρ υ θ : ℝ) :
    1 ≤ ‖fixedOccupancySlope η τ ρ υ θ‖ := by
  have hh := Complex.re_le_norm (fixedOccupancySlope η τ ρ υ θ)
  simpa only [fixedOccupancySlope, Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero] using hh

theorem fixedOccupancy_jacobian_norm_le_regularSlope (s : ℂ) (η τ ρ υ θ : ℝ) :
    ‖1 + physicalPhaseAngleSlope s (fixedOccupancyAngle η τ ρ υ θ)‖ ≤
      ‖fixedOccupancyRegularSlope s η τ ρ υ θ‖ := by
  have he : fixedOccupancyRegularSlope s η τ ρ υ θ =
      (1 + physicalPhaseAngleSlope s (fixedOccupancyAngle η τ ρ υ θ)) * fixedOccupancySlope η τ ρ υ θ := by
    simp only [fixedOccupancyRegularSlope, physicalPhaseAngleSlope, neg_div,
      sub_eq_add_neg]
  rw [he, norm_mul]
  exact le_mul_of_one_le_right (norm_nonneg _) (fixedOccupancySlope_norm_ge_one η τ ρ υ θ)

/-- One common independent branch-weight envelope for all actual
coordinates, including the full negative branch sliver. -/
theorem exists_actual_whole_arc_jacobian_weight (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ k, θ k ∈ Icc (-Real.pi - δ) δ) →
      ∀ i : Fin N,
        ‖1 + actualPhaseSlope (isotropicRadialParameter α ε) η τ ξ θ i‖ ≤
          C / Real.sqrt (|θ i + b| + ε) := by
  obtain ⟨δ, C, hδ, hδ1, hC, hbound⟩ :=
    exists_fixedOccupancy_whole_arc_derivative α b η hα hb hpoint hη hwidth
  refine ⟨δ, C, hδ, hδ1, hC, ?_⟩
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
