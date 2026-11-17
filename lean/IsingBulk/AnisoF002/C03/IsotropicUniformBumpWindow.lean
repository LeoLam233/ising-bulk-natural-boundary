import IsingBulk.AnisoF002.C03.IsotropicWholeArcDerivative

/-!
# A geometric branch window selected before the bump width

The lower-branch plateau is controlled by sin b, not by the transition
width η. Consequently the branch and regular angular patches can be
fixed before η; only derivative constants and later τ-smallness depend
on the smooth bump width.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric Filter

theorem lower_branch_plateau_geometric_window (b η u : ℝ) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) (hu : |u| ≤ Real.sin b / 2) :
    upperPeriodicBump η (-b + u) = 0 ∧ lowerPeriodicBump η (-b + u) = 1 := by
  have hd := Real.abs_sin_sub_sin_le (b - u) b
  rw [show b - u - b = -u by ring, abs_neg] at hd
  have hsin : 2 * η ≤ Real.sin (b - u) := by
    linarith only [(abs_le.mp (hd.trans hu)).1, hwidth]
  have hsneg : Real.sin (-b + u) = -Real.sin (b - u) := by
    rw [show -b + u = -(b - u) by ring, Real.sin_neg]
  refine ⟨upperPeriodicBump_zero hη (by rw [hsneg]; linarith only [hsin, hη]), ?_⟩
  unfold lowerPeriodicBump
  rw [show -(-b + u) = b - u by ring]
  exact upperPeriodicBump_one hη hsin

theorem lower_branch_plateau_geometric_derivatives (b η u : ℝ) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) (hu : |u| < Real.sin b / 2) :
    deriv (upperPeriodicBump η) (-b + u) = 0 ∧
      deriv (lowerPeriodicBump η) (-b + u) = 0 := by
  have hnear : ∀ᶠ x in 𝓝 (-b + u), |x + b| < Real.sin b / 2 := by
    have hc : ContinuousAt (fun x : ℝ => |x + b|) (-b + u) := by fun_prop
    have hlt : |-b + u + b| < Real.sin b / 2 := by rwa [show -b + u + b = u by ring]
    exact hc.eventually (gt_mem_nhds hlt)
  have hp : upperPeriodicBump η =ᶠ[𝓝 (-b + u)] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hnear] with x hx
    have hh := (lower_branch_plateau_geometric_window b η (x + b) hη hwidth hx.le).1
    rwa [show -b + (x + b) = x by ring] at hh
  have hm : lowerPeriodicBump η =ᶠ[𝓝 (-b + u)] (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [hnear] with x hx
    have hh := (lower_branch_plateau_geometric_window b η (x + b) hη hwidth hx.le).2
    rwa [show -b + (x + b) = x by ring] at hh
  exact ⟨by simpa only [deriv_const] using hp.deriv_eq,
    by simpa only [deriv_const] using hm.deriv_eq⟩

theorem fixedOccupancyAngle_geometric_branch (b η τ ρ υ u : ℝ) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) (hu : |u| ≤ Real.sin b / 2) :
    fixedOccupancyAngle η τ ρ υ (-b + u) =
      ((-b + u : ℝ) : ℂ) - Complex.I * ((τ * ρ : ℝ) : ℂ) := by
  obtain ⟨hp, hm⟩ := lower_branch_plateau_geometric_window b η u hη hwidth hu
  simp only [fixedOccupancyAngle, hp, hm, mul_one, mul_zero, sub_zero]

theorem fixedOccupancyRegularSlope_geometric_branch (α b ε η τ ρ υ u : ℝ)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) (hu : |u| < Real.sin b / 2) :
    fixedOccupancyRegularSlope (isotropicRadialParameter α ε) η τ ρ υ (-b + u) =
      branchCoordinateSlope α b ε (τ * ρ) u := by
  obtain ⟨hp, hm⟩ := lower_branch_plateau_geometric_derivatives b η u hη hwidth hu
  have hsl : fixedOccupancySlope η τ ρ υ (-b + u) = 1 := by
    simp only [fixedOccupancySlope, hp, hm, mul_zero, sub_zero, Complex.ofReal_zero]
  rw [fixedOccupancyRegularSlope, hsl, mul_one,
    fixedOccupancyAngle_geometric_branch b η τ ρ υ u hη hwidth hu.le]
  rfl

theorem exists_whole_arc_derivative_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ρ υ : ℝ,
        τ ∈ Icc 0 δ → ρ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
      ∀ θ ∈ Icc (-Real.pi - δ) δ,
        HasDerivAt (fixedOccupancyRegularCurve (isotropicRadialParameter α ε) η τ ρ υ)
          (fixedOccupancyRegularSlope (isotropicRadialParameter α ε) η τ ρ υ θ) θ ∧
        ‖fixedOccupancyRegularSlope (isotropicRadialParameter α ε) η τ ρ υ θ‖ ≤
          C / Real.sqrt (|θ + b| + ε) := by
  obtain ⟨RB, K, hRB, _, hK, hbranch⟩ :=
    exists_branch_coordinate_derivative_majorant α b hα hb hpoint
  have hsin : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  let R := min RB (Real.sin b / 4)
  have hR : 0 < R := by dsimp [R]; positivity
  have hRhalf : R < Real.sin b / 2 :=
    (min_le_right _ _).trans_lt (by linarith only [hsin])
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  rw [Real.cos_pi] at hcos
  have hS : 0 < 2 * Real.cos α := by linarith only [hcos, hpoint]
  obtain ⟨δA, A, hδA, _, hA, haway⟩ := exists_fixedOccupancy_away_phase_bound
    (2 * Real.cos α) b R hS ⟨hb.1.le, hb.2.le⟩ hpoint hR
  let δ := min 1 (min RB (δA / 4))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδB : δ ≤ RB := (min_le_right _ _).trans (min_le_left _ _)
  have hδA4 : δ ≤ δA / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hδAle : δ ≤ δA := by linarith only [hδA4, hδA]
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro η hη hwidth
  obtain ⟨L, hL, hpD, hmD, _, _⟩ := actual_bump_global_first_bounds η
  let B := (1 + Real.exp 1 * A) * (1 + 2 * L)
  let C := max K (B * Real.sqrt (Real.pi + 2))
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨C, hK.trans_le (le_max_left _ _), ?_⟩
  intro ε hε hεδ τ ρ υ hτ hρ hυ θ hθ
  have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)
  refine ⟨fixedOccupancyRegularCurve_hasDerivAt _ hrad.2.2.2.1 η τ ρ υ θ hη hτ.1 hρ.1 hυ.1, ?_⟩
  by_cases hlocal : |θ + b| ≤ R
  · have hdepth : τ * ρ ∈ Icc 0 RB := by
      refine ⟨mul_nonneg hτ.1 hρ.1, ?_⟩
      exact (mul_le_of_le_one_right hτ.1 hρ.2).trans (hτ.2.trans hδB)
    have he := fixedOccupancyRegularSlope_geometric_branch α b ε η τ ρ υ (θ + b)
      hη hwidth (hlocal.trans_lt hRhalf)
    rw [show -b + (θ + b) = θ by ring] at he
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
