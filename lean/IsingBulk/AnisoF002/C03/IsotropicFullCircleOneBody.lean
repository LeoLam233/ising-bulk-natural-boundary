import IsingBulk.AnisoF002.C03.IsotropicUniformBumpWindow
import IsingBulk.AnisoF002.C03.IsotropicBranchIntegral
import IsingBulk.AnisoF002.RegularTail.PhysicalFactors

/-!
# A genuine full-circle one-body L1 majorant

The two actual physical branch points have their true inverse-square-
root weights. The regular compact complement is bounded from the exact
spectral discriminant. Both full occupancies are retained; reflection
transfers the negative half-circle estimate to the positive half.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology
open Set Metric MeasureTheory
open IsingBulk.AnisoF002.RegularTail

theorem isotropic_oneBody_norm (s w : ℂ) :
    ‖2 * isotropicInteriorRoot (s, w) / (1 - isotropicInteriorRoot (s, w) ^ 2)‖ =
      ‖Complex.sin (upperPhysicalPhase (isotropicDispersion (s, w)))‖⁻¹ := by
  have hh := oneBody_exp_eq_inv_sinh (upperPhysicalPhase (isotropicDispersion (s, w)) * Complex.I)
  rw [upperPhysicalPhase_exp] at hh
  change ‖2 * upperEdgeRoot (isotropicDispersion (s, w)) /
    (1 - upperEdgeRoot (isotropicDispersion (s, w)) ^ 2)‖ = _
  rw [hh, norm_div, norm_one, Complex.sinh_mul_I, norm_mul, Complex.norm_I, mul_one, one_div]

theorem fixedOccupancyAngle_reflection (η τ ρ υ θ : ℝ) :
    fixedOccupancyAngle η τ ρ υ θ = -fixedOccupancyAngle η τ υ ρ (-θ) := by
  simp only [fixedOccupancyAngle, lowerPeriodicBump, neg_neg, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_sub]
  ring

/-- Uniform true inverse-sine envelope on the complete negative
half-circle, including both sides of its physical branch point. -/
theorem exists_half_circle_oneBody_bound (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ρ υ : ℝ, τ ∈ Icc 0 δ → ρ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
      ∀ θ ∈ Icc (-Real.pi) 0,
        ‖2 * isotropicInteriorRoot (isotropicRadialParameter α ε, fixedOccupancyAngle η τ ρ υ θ) /
          (1 - isotropicInteriorRoot (isotropicRadialParameter α ε, fixedOccupancyAngle η τ ρ υ θ) ^ 2)‖ ≤
          C * branchWeight ε (θ + b) := by
  obtain ⟨RB, cB, _, hRB, _, hcB, _, hbranch⟩ :=
    exists_isotropic_branch_sine_bounds α b hα hb hpoint
  have hsinb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  let R := min RB (Real.sin b / 4)
  have hR : 0 < R := lt_min hRB (by positivity)
  have hRRB : R ≤ RB := min_le_left _ _
  have hRsin : R ≤ Real.sin b / 2 := (min_le_right _ _).trans (by linarith only [hsinb])
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  rw [Real.cos_pi] at hcos
  have hS : 0 < 2 * Real.cos α := by linarith only [hcos, hpoint]
  obtain ⟨δA, A, hδA, _, hA, haway⟩ := exists_fixedOccupancy_away_phase_bound
    (2 * Real.cos α) b R hS ⟨hb.1.le, hb.2.le⟩ hpoint hR
  let δ := min 1 (min RB (δA / 4))
  let C := max (1 / cB) (A * Real.sqrt (Real.pi + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδB : δ ≤ RB := (min_le_right _ _).trans (min_le_left _ _)
  have hδA4 : δ ≤ δA / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hδAle : δ ≤ δA := by linarith only [hδA4, hδA]
  have hC : 0 < C := (one_div_pos.mpr hcB).trans_le (le_max_left _ _)
  refine ⟨δ, C, hδ, hδ1, hC, ?_⟩
  intro η hη hwidth ε hε hεδ τ ρ υ hτ hρ hυ θ hθ
  rw [isotropic_oneBody_norm]
  let u := θ + b
  have hF : 0 < |u| + ε := add_pos_of_nonneg_of_pos (abs_nonneg u) hε
  have hsF : 0 < Real.sqrt (|u| + ε) := Real.sqrt_pos.mpr hF
  have hτρ : 0 ≤ τ * ρ := mul_nonneg hτ.1 hρ.1
  have hτρle : τ * ρ ≤ δ :=
    (show τ * ρ ≤ τ by nlinarith only [hρ.2, hτ.1]).trans hτ.2
  rw [branchWeight, mul_one_div]
  change _ ≤ C / Real.sqrt (|u| + ε)
  by_cases hlocal : |u| ≤ R
  · have hangle : fixedOccupancyAngle η τ ρ υ θ =
        ((-b + u : ℝ) : ℂ) - Complex.I * ((τ * ρ : ℝ) : ℂ) := by
      have hh := fixedOccupancyAngle_geometric_branch b η τ ρ υ u hη hwidth (hlocal.trans hRsin)
      simpa only [u, show -b + (θ + b) = θ by ring] using hh
    have hlo := (hbranch ε hε (hεδ.trans hδB) u (τ * ρ) (hlocal.trans hRRB)
      ⟨hτρ, hτρle.trans hδB⟩).1
    have hden : cB * Real.sqrt (|u| + ε) ≤
        ‖Complex.sin (upperPhysicalPhase (isotropicDispersion
          (isotropicRadialParameter α ε, fixedOccupancyAngle η τ ρ υ θ)))‖ := by
      rw [hangle]
      exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith only [hτρ])) hcB.le).trans hlo
    calc
      _ ≤ 1 / (cB * Real.sqrt (|u| + ε)) := by
        simpa only [one_div] using one_div_le_one_div_of_le (mul_pos hcB hsF) hden
      _ = (1 / cB) / Real.sqrt (|u| + ε) := by ring
      _ ≤ C / Real.sqrt (|u| + ε) := div_le_div_of_nonneg_right (le_max_left _ _) hsF.le
  · have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)
    have hsnear : dist (isotropicRadialParameter α ε) ((2 * Real.cos α : ℝ) : ℂ) ≤ δA :=
      hrad.2.2.2.2.trans (by linarith only [hεδ, hδA4])
    have hθA : θ ∈ Icc (-Real.pi - δA) δA :=
      ⟨by linarith only [hθ.1, hδA], hθ.2.trans hδA.le⟩
    have hp := haway _ hsnear η τ ρ υ θ ⟨hτ.1, hτ.2.trans hδAle⟩ hρ hυ hθA
      (lt_of_not_ge hlocal).le
    have hu : |u| ≤ Real.pi := by
      apply abs_le.mpr
      dsimp [u]
      constructor <;> linarith only [hθ.1, hθ.2, hb.1, hb.2]
    apply hp.trans
    apply (le_div_iff₀ hsF).mpr
    exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (show |u| + ε ≤ Real.pi + 1 by linarith only [hu, hεδ, hδ1])) hA.le).trans (le_max_right _ _)

def fullCircleOneBodyMajorant (b C ε θ : ℝ) : ℝ :=
  C * (1 + branchWeight ε (θ + b) + branchWeight ε (θ - b))

theorem fullCircleOneBodyMajorant_nonneg {C : ℝ} (hC : 0 ≤ C) (b ε θ : ℝ) :
    0 ≤ fullCircleOneBodyMajorant b C ε θ :=
  mul_nonneg hC (add_nonneg (add_nonneg zero_le_one (branchWeight_nonneg ε _))
    (branchWeight_nonneg ε _))

theorem fullCircleOneBodyMajorant_continuous (b C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fullCircleOneBodyMajorant b C ε) :=
  continuous_const.mul ((continuous_const.add
    ((branchWeight_continuous hε).comp (continuous_id.add continuous_const))).add
    ((branchWeight_continuous hε).comp (continuous_id.sub continuous_const)))

/-- The entire physical angular circle is controlled by one pair of
integrable branch weights, uniformly in both population fractions. -/
theorem exists_full_circle_oneBody_pointwise (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ρ υ : ℝ, τ ∈ Icc 0 δ → ρ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
      ∀ θ ∈ Icc (-Real.pi) Real.pi,
        ‖2 * isotropicInteriorRoot (isotropicRadialParameter α ε, fixedOccupancyAngle η τ ρ υ θ) /
          (1 - isotropicInteriorRoot (isotropicRadialParameter α ε, fixedOccupancyAngle η τ ρ υ θ) ^ 2)‖ ≤
          fullCircleOneBodyMajorant b C ε θ := by
  obtain ⟨δ, C, hδ, hδ1, hC, hhalf⟩ := exists_half_circle_oneBody_bound α b hα hb hpoint
  refine ⟨δ, C, hδ, hδ1, hC, ?_⟩
  intro η hη hwidth ε hε hεδ τ ρ υ hτ hρ hυ θ hθ
  by_cases hθ0 : θ ≤ 0
  · apply (hhalf η hη hwidth ε hε hεδ τ ρ υ hτ hρ hυ θ ⟨hθ.1, hθ0⟩).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    linarith only [branchWeight_nonneg ε (θ - b)]
  · have hh := hhalf η hη hwidth ε hε hεδ τ υ ρ hτ hυ hρ (-θ)
      (show -θ ∈ Icc (-Real.pi) 0 by constructor <;> linarith only [hθ.2, hθ0])
    have hroot : isotropicInteriorRoot (isotropicRadialParameter α ε, fixedOccupancyAngle η τ ρ υ θ) =
        isotropicInteriorRoot (isotropicRadialParameter α ε, fixedOccupancyAngle η τ υ ρ (-θ)) := by
      rw [fixedOccupancyAngle_reflection η τ ρ υ θ]
      simp only [isotropicInteriorRoot, isotropicDispersion, Complex.cos_neg]
    rw [hroot]
    have hw : branchWeight ε (-θ + b) = branchWeight ε (θ - b) := by
      simp only [branchWeight, show -θ + b = -(θ - b) by ring, abs_neg]
    rw [hw] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    linarith only [branchWeight_nonneg ε (θ + b)]

end IsingBulk.AnisoF002.Isotropic
