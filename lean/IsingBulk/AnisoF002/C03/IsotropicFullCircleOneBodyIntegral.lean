import IsingBulk.AnisoF002.C03.IsotropicFullCircleOneBody

/-!
# Uniform L1 control of the complete physical one-body majorant

Both shifted inverse-square-root weights are integrated on the actual
full angular interval. Their uniform bound is independent of epsilon,
the particle number, and both population fractions.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology
open Set MeasureTheory

theorem branchWeight_shifted_full_period_bound (c ε : ℝ) (hε : 0 < ε) :
    (∫ θ in (-Real.pi)..Real.pi, branchWeight ε (θ + c)) ≤ 12 * Real.pi := by
  rw [intervalIntegral.integral_comp_add_right]
  have hh := branchWeight_shell_integral_bound c (Real.pi / 2) ε (by positivity) hε
  have he₁ : c - 2 * (Real.pi / 2) = -Real.pi + c := by ring
  have he₂ : c + 2 * (Real.pi / 2) = Real.pi + c := by ring
  rw [he₁, he₂] at hh
  have hs : 1 ≤ Real.sqrt (|c| + Real.pi / 2 + ε) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [abs_nonneg c, Real.two_le_pi, hε])
  apply hh.trans
  apply (div_le_iff₀ (zero_lt_one.trans_le hs)).mpr
  nlinarith only [hs, Real.pi_pos]

theorem fullCircleOneBodyMajorant_integral_bound (b C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    (∫ θ in Icc (-Real.pi) Real.pi, fullCircleOneBodyMajorant b C ε θ) ≤
      26 * Real.pi * C := by
  have hA : IntervalIntegrable (fun θ => branchWeight ε (θ + b)) volume (-Real.pi) Real.pi :=
    ((branchWeight_continuous hε).comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun θ => branchWeight ε (θ - b)) volume (-Real.pi) Real.pi :=
    ((branchWeight_continuous hε).comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [Real.pi_pos])]
  change (∫ θ in (-Real.pi)..Real.pi,
    C * (1 + branchWeight ε (θ + b) + branchWeight ε (θ - b))) ≤ _
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_const.add hA) hB,
    intervalIntegral.integral_add intervalIntegrable_const hA, intervalIntegral.integral_const]
  have ha := branchWeight_shifted_full_period_bound b ε hε
  have hb : (∫ θ in (-Real.pi)..Real.pi, branchWeight ε (θ - b)) ≤ 12 * Real.pi := by
    simpa only [sub_eq_add_neg] using branchWeight_shifted_full_period_bound (-b) ε hε
  simp only [smul_eq_mul, mul_one]
  calc
    _ ≤ C * (Real.pi - -Real.pi + 12 * Real.pi + 12 * Real.pi) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl ha) hb) hC
    _ = _ := by ring

/-- The actual full-circle one-body factors have a continuous nonnegative
majorant of uniformly bounded integral, with constants selected before
all particle numbers, radial parameters, and occupancy values. -/
theorem exists_full_circle_oneBody_L1_majorant (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ C L : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 < L ∧
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        Continuous (fullCircleOneBodyMajorant b C ε) ∧
        (∀ θ : ℝ, 0 ≤ fullCircleOneBodyMajorant b C ε θ) ∧
        IntegrableOn (fullCircleOneBodyMajorant b C ε) (Icc (-Real.pi) Real.pi) volume ∧
        (∫ θ in Icc (-Real.pi) Real.pi, fullCircleOneBodyMajorant b C ε θ) ≤ L ∧
        ∀ τ ρ υ : ℝ, τ ∈ Icc 0 δ → ρ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
        ∀ θ ∈ Icc (-Real.pi) Real.pi,
          ‖2 * isotropicInteriorRoot (isotropicRadialParameter α ε, fixedOccupancyAngle η τ ρ υ θ) /
            (1 - isotropicInteriorRoot (isotropicRadialParameter α ε, fixedOccupancyAngle η τ ρ υ θ) ^ 2)‖ ≤
            fullCircleOneBodyMajorant b C ε θ := by
  obtain ⟨δ, C, hδ, hδ1, hC, hbound⟩ := exists_full_circle_oneBody_pointwise α b hα hb hpoint
  refine ⟨δ, C, 26 * Real.pi * C, hδ, hδ1, hC, by positivity, ?_⟩
  intro η hη hwidth ε hε hεδ
  have hc := fullCircleOneBodyMajorant_continuous b C hε
  exact ⟨hc, fullCircleOneBodyMajorant_nonneg hC.le b ε,
    hc.continuousOn.integrableOn_Icc, fullCircleOneBodyMajorant_integral_bound b C ε hC.le hε,
    hbound η hη hwidth ε hε hεδ⟩

end IsingBulk.AnisoF002.Isotropic
