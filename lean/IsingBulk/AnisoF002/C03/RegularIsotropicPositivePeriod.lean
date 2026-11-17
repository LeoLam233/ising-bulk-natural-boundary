import IsingBulk.AnisoF002.C03.IsotropicFullCircleOneBodyIntegral

/-!
# The one-body majorant on the literal [0,2 pi] integration box

A sum of two translated full-circle envelopes avoids any nonsmooth
choice of angular representative. Exact physical periodicity supplies
the estimate; both envelopes have uniformly bounded integrals.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set MeasureTheory
open scoped Topology

def positivePeriodOneBodyMajorant (b C ε θ : ℝ) : ℝ :=
  fullCircleOneBodyMajorant b C ε θ + fullCircleOneBodyMajorant b C ε (θ - 2 * Real.pi)

theorem fixedOccupancyAngle_add_two_pi (η τ ρ υ θ : ℝ) :
    fixedOccupancyAngle η τ ρ υ (θ + 2 * Real.pi) =
      fixedOccupancyAngle η τ ρ υ θ + 2 * (Real.pi : ℂ) := by
  simp only [fixedOccupancyAngle, upperPeriodicBump_periodic η θ,
    lowerPeriodicBump_periodic η θ, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

theorem fixedOccupancyRoot_sub_two_pi (S : ℂ) (η τ ρ υ θ : ℝ) :
    isotropicInteriorRoot (S, fixedOccupancyAngle η τ ρ υ θ) =
      isotropicInteriorRoot (S, fixedOccupancyAngle η τ ρ υ (θ - 2 * Real.pi)) := by
  have hw := fixedOccupancyAngle_add_two_pi η τ ρ υ (θ - 2 * Real.pi)
  rw [sub_add_cancel] at hw
  rw [hw]
  simp only [isotropicInteriorRoot, isotropicDispersion, Complex.cos_add_two_pi]

theorem branchWeight_positive_period_bound (c ε : ℝ) (hε : 0 < ε) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), branchWeight ε (θ + c)) ≤ 12 * Real.pi := by
  have hh := branchWeight_shifted_full_period_bound (c + Real.pi) ε hε
  rw [intervalIntegral.integral_comp_add_right] at hh ⊢
  rw [show -Real.pi + (c + Real.pi) = c by ring,
    show Real.pi + (c + Real.pi) = 2 * Real.pi + c by ring] at hh
  simpa only [zero_add] using hh

theorem fullCircleOneBodyMajorant_positive_shift_integral (b C ε a : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), fullCircleOneBodyMajorant b C ε (θ + a)) ≤
      26 * Real.pi * C := by
  have hA : IntervalIntegrable (fun θ => branchWeight ε (θ + (a + b))) volume 0 (2 * Real.pi) :=
    ((branchWeight_continuous hε).comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun θ => branchWeight ε (θ + (a - b))) volume 0 (2 * Real.pi) :=
    ((branchWeight_continuous hε).comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have he : (fun θ => fullCircleOneBodyMajorant b C ε (θ + a)) =
      fun θ => C * (1 + branchWeight ε (θ + (a + b)) + branchWeight ε (θ + (a - b))) := by
    funext θ
    unfold fullCircleOneBodyMajorant
    rw [show θ + a + b = θ + (a + b) by ring,
      show θ + a - b = θ + (a - b) by ring]
  rw [he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_const.add hA) hB,
    intervalIntegral.integral_add intervalIntegrable_const hA, intervalIntegral.integral_const]
  have ha := branchWeight_positive_period_bound (a + b) ε hε
  have hb := branchWeight_positive_period_bound (a - b) ε hε
  simp only [sub_zero, smul_eq_mul, mul_one]
  calc
    _ ≤ C * (2 * Real.pi + 12 * Real.pi + 12 * Real.pi) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl ha) hb) hC
    _ = _ := by ring

theorem positivePeriodOneBodyMajorant_continuous (b C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (positivePeriodOneBodyMajorant b C ε) :=
  (fullCircleOneBodyMajorant_continuous b C hε).add
    ((fullCircleOneBodyMajorant_continuous b C hε).comp (continuous_id.sub continuous_const))

theorem positivePeriodOneBodyMajorant_nonneg {C : ℝ} (hC : 0 ≤ C) (b ε θ : ℝ) :
    0 ≤ positivePeriodOneBodyMajorant b C ε θ :=
  add_nonneg (fullCircleOneBodyMajorant_nonneg hC b ε θ)
    (fullCircleOneBodyMajorant_nonneg hC b ε (θ - 2 * Real.pi))

theorem positivePeriodOneBodyMajorant_integral (b C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    (∫ θ in Icc 0 (2 * Real.pi), positivePeriodOneBodyMajorant b C ε θ) ≤ 52 * Real.pi * C := by
  have hA : IntervalIntegrable (fullCircleOneBodyMajorant b C ε) volume 0 (2 * Real.pi) :=
    (fullCircleOneBodyMajorant_continuous b C hε).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun θ => fullCircleOneBodyMajorant b C ε (θ - 2 * Real.pi)) volume 0 (2 * Real.pi) :=
    ((fullCircleOneBodyMajorant_continuous b C hε).comp
      (continuous_id.sub continuous_const)).intervalIntegrable _ _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity)]
  unfold positivePeriodOneBodyMajorant
  rw [intervalIntegral.integral_add hA hB]
  have ha : (∫ θ in (0 : ℝ)..(2 * Real.pi), fullCircleOneBodyMajorant b C ε θ) ≤ 26 * Real.pi * C := by
    simpa only [add_zero] using fullCircleOneBodyMajorant_positive_shift_integral b C ε 0 hC hε
  have hb : (∫ θ in (0 : ℝ)..(2 * Real.pi), fullCircleOneBodyMajorant b C ε (θ - 2 * Real.pi)) ≤ 26 * Real.pi * C := by
    simpa only [sub_eq_add_neg] using fullCircleOneBodyMajorant_positive_shift_integral b C ε (-(2 * Real.pi)) hC hε
  linarith

theorem exists_positive_period_oneBody_majorant (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        Continuous (positivePeriodOneBodyMajorant b C ε) ∧
        (∀ θ : ℝ, 0 ≤ positivePeriodOneBodyMajorant b C ε θ) ∧
        IntegrableOn (positivePeriodOneBodyMajorant b C ε) (Icc 0 (2 * Real.pi)) volume ∧
        (∫ θ in Icc 0 (2 * Real.pi), positivePeriodOneBodyMajorant b C ε θ) ≤ 52 * Real.pi * C ∧
        ∀ τ ρ υ : ℝ, τ ∈ Icc 0 δ → ρ ∈ Icc 0 1 → υ ∈ Icc 0 1 →
        ∀ θ ∈ Icc 0 (2 * Real.pi),
          ‖2 * isotropicInteriorRoot (isotropicRadialParameter α ε, fixedOccupancyAngle η τ ρ υ θ) /
            (1 - isotropicInteriorRoot (isotropicRadialParameter α ε, fixedOccupancyAngle η τ ρ υ θ) ^ 2)‖ ≤
            positivePeriodOneBodyMajorant b C ε θ := by
  obtain ⟨δ, C, hδ, hδ1, hC, hbound⟩ := exists_full_circle_oneBody_pointwise α b hα hb hpoint
  refine ⟨δ, C, hδ, hδ1, hC, ?_⟩
  intro η hη hwidth ε hε hεδ
  have hcont := positivePeriodOneBodyMajorant_continuous b C hε
  refine ⟨hcont, positivePeriodOneBodyMajorant_nonneg hC.le b ε,
    hcont.continuousOn.integrableOn_Icc, positivePeriodOneBodyMajorant_integral b C ε hC.le hε, ?_⟩
  intro τ ρ υ hτ hρ hυ θ hθ
  by_cases hθπ : θ ≤ Real.pi
  · have hh := hbound η hη hwidth ε hε hεδ τ ρ υ hτ hρ hυ θ
      ⟨by linarith [Real.pi_pos, hθ.1], hθπ⟩
    exact hh.trans (le_add_of_nonneg_right (fullCircleOneBodyMajorant_nonneg hC.le b ε _))
  · have hh := hbound η hη hwidth ε hε hεδ τ ρ υ hτ hρ hυ (θ - 2 * Real.pi)
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos, hθ.2]⟩
    rw [← fixedOccupancyRoot_sub_two_pi] at hh
    exact hh.trans (le_add_of_nonneg_left (fullCircleOneBodyMajorant_nonneg hC.le b ε θ))

end
end IsingBulk.AnisoF002.Isotropic
