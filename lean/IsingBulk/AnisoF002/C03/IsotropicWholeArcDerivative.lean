import IsingBulk.AnisoF002.C03.IsotropicAwayDiscriminant

/-!
# Integrable physical coordinate derivative on the whole right arc

The actual branch estimate and the compact discriminant margin are
combined on one common radial neighborhood, uniformly over every pair
of full population fractions and every allowed deformation size.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric Filter

theorem lower_branch_plateau_derivatives (b η u : ℝ) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) (hu : |u| < η) :
    deriv (upperPeriodicBump η) (-b + u) = 0 ∧
      deriv (lowerPeriodicBump η) (-b + u) = 0 := by
  have hnear : ∀ᶠ x in 𝓝 (-b + u), |x + b| < η := by
    have hc : ContinuousAt (fun x : ℝ => |x + b|) (-b + u) := by fun_prop
    have hlt : |-b + u + b| < η := by rwa [show -b + u + b = u by ring]
    exact hc.eventually (gt_mem_nhds hlt)
  have hp : upperPeriodicBump η =ᶠ[𝓝 (-b + u)] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hnear] with x hx
    have hh := (lower_branch_plateau_window b η (x + b) hη hwidth hx.le).1
    rwa [show -b + (x + b) = x by ring] at hh
  have hm : lowerPeriodicBump η =ᶠ[𝓝 (-b + u)] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [hnear] with x hx
    have hh := (lower_branch_plateau_window b η (x + b) hη hwidth hx.le).2
    rwa [show -b + (x + b) = x by ring] at hh
  exact ⟨by simpa only [deriv_const] using hp.deriv_eq,
    by simpa only [deriv_const] using hm.deriv_eq⟩

theorem fixedOccupancyRegularSlope_on_branch (α b ε η τ ρ υ u : ℝ)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) (hu : |u| < η) :
    fixedOccupancyRegularSlope (isotropicRadialParameter α ε) η τ ρ υ (-b + u) =
      branchCoordinateSlope α b ε (τ * ρ) u := by
  obtain ⟨hp, hm⟩ := lower_branch_plateau_derivatives b η u hη hwidth hu
  have hsl : fixedOccupancySlope η τ ρ υ (-b + u) = 1 := by
    simp only [fixedOccupancySlope, hp, hm, mul_zero, sub_zero, Complex.ofReal_zero]
  rw [fixedOccupancyRegularSlope, hsl, mul_one,
    fixedOccupancyAngle_on_branch b η τ ρ υ u hη hwidth hu.le]
  rfl

/-- One fixed integrable derivative majorant covers the complete right
arc and its endpoint slivers, including the branch and the negative
branch segment. Both full population fractions range over [0,1]. -/
theorem exists_fixedOccupancy_whole_arc_derivative (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ρ υ : ℝ,
        τ ∈ Icc 0 δ → ρ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
      ∀ θ ∈ Icc (-Real.pi - δ) δ,
        HasDerivAt (fixedOccupancyRegularCurve (isotropicRadialParameter α ε) η τ ρ υ)
          (fixedOccupancyRegularSlope (isotropicRadialParameter α ε) η τ ρ υ θ) θ ∧
        ‖fixedOccupancyRegularSlope (isotropicRadialParameter α ε) η τ ρ υ θ‖ ≤
          C / Real.sqrt (|θ + b| + ε) := by
  obtain ⟨RB, K, hRB, hRB1, hK, hbranch⟩ :=
    exists_branch_coordinate_derivative_majorant α b hα hb hpoint
  let R := min RB (η / 2)
  have hR : 0 < R := lt_min hRB (by positivity)
  have hRη : R < η := (min_le_right _ _).trans_lt (by linarith)
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  rw [Real.cos_pi] at hcos
  have hS : 0 < 2 * Real.cos α := by linarith only [hcos, hpoint]
  obtain ⟨δA, A, hδA, _, hA, haway⟩ := exists_fixedOccupancy_away_phase_bound
    (2 * Real.cos α) b R hS ⟨hb.1.le, hb.2.le⟩ hpoint hR
  obtain ⟨L, hL, hpD, hmD, _, _⟩ := actual_bump_global_first_bounds η
  let δ := min 1 (min RB (δA / 4))
  let B := (1 + Real.exp 1 * A) * (1 + 2 * L)
  let C := max K (B * Real.sqrt (Real.pi + 2))
  have hδ : 0 < δ := lt_min zero_lt_one (lt_min hRB (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδB : δ ≤ RB := (min_le_right _ _).trans (min_le_left _ _)
  have hδA4 : δ ≤ δA / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hδAle : δ ≤ δA := by linarith only [hδA4, hδA]
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨δ, C, hδ, hδ1, hK.trans_le (le_max_left _ _), ?_⟩
  intro ε hε hεδ τ ρ υ hτ hρ hυ θ hθ
  have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)
  refine ⟨fixedOccupancyRegularCurve_hasDerivAt _ hrad.2.2.2.1 η τ ρ υ θ hη hτ.1 hρ.1 hυ.1, ?_⟩
  by_cases hlocal : |θ + b| ≤ R
  · have hdepth : τ * ρ ∈ Icc 0 RB := by
      refine ⟨mul_nonneg hτ.1 hρ.1, ?_⟩
      calc
        _ ≤ τ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hρ.2 hτ.1
        _ ≤ RB := hτ.2.trans hδB
    have he : fixedOccupancyRegularSlope (isotropicRadialParameter α ε) η τ ρ υ θ =
        branchCoordinateSlope α b ε (τ * ρ) (θ + b) := by
      have hh := fixedOccupancyRegularSlope_on_branch α b ε η τ ρ υ (θ + b)
        hη hwidth (hlocal.trans_lt hRη)
      rwa [show -b + (θ + b) = θ by ring] at hh
    rw [he]
    exact ((hbranch ε hε (hεδ.trans hδB) _ hdepth (θ + b)
      (hlocal.trans (min_le_left _ _))).2).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  · have hfar : R ≤ |θ + b| := (lt_of_not_ge hlocal).le
    have hsnear : dist (isotropicRadialParameter α ε) ((2 * Real.cos α : ℝ) : ℂ) ≤ δA :=
      hrad.2.2.2.2.trans (by linarith only [hεδ, hδA4])
    have hθA : θ ∈ Icc (-Real.pi - δA) δA :=
      ⟨by linarith only [hθ.1, hδAle], hθ.2.trans hδAle⟩
    have hphase := haway _ hsnear η τ ρ υ θ ⟨hτ.1, hτ.2.trans hδAle⟩ hρ hυ hθA hfar
    have hbound : ‖fixedOccupancyRegularSlope (isotropicRadialParameter α ε) η τ ρ υ θ‖ ≤ B :=
      fixedOccupancyRegularSlope_norm_bound _ η τ ρ υ θ L A ⟨hτ.1, hτ.2.trans hδ1⟩
        hρ hυ hL.le (hpD θ) (hmD θ) hphase
    have hu : |θ + b| ≤ Real.pi + 1 := by
      apply abs_le.mpr
      constructor <;> linarith only [hθ.1, hθ.2, hb.1, hb.2, hδ1]
    have hsqrt : Real.sqrt (|θ + b| + ε) ≤ Real.sqrt (Real.pi + 2) :=
      Real.sqrt_le_sqrt (by linarith only [hu, hεδ, hδ1])
    have hpos : 0 < Real.sqrt (|θ + b| + ε) := Real.sqrt_pos.mpr (by positivity)
    apply hbound.trans
    apply (le_div_iff₀ hpos).mpr
    exact (mul_le_mul_of_nonneg_left hsqrt hB.le).trans (le_max_right _ _)

end IsingBulk.AnisoF002.Isotropic
