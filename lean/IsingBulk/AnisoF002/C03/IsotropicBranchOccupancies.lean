import IsingBulk.AnisoF002.C03.IsotropicBranchCoordinateScales
import IsingBulk.AnisoF002.C03.IsotropicRightHomotopy

/-!
# Actual occupancy fractions on the branch plateau

The populations are the full sums of the constructed smooth bumps.
Every branch-window coordinate is identified with the same outward
physical curve. No lower population bound or particle restriction is used.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def actualUpperOccupancy {N : ℕ} (η : ℝ) (θ : Fin N → ℝ) : ℝ :=
  (∑ j, upperPeriodicBump η (θ j)) / N

def actualLowerOccupancy {N : ℕ} (η : ℝ) (θ : Fin N → ℝ) : ℝ :=
  (∑ j, lowerPeriodicBump η (θ j)) / N

theorem actualUpperOccupancy_mem_Icc {N : ℕ} (hN : 0 < N) (η : ℝ) (θ : Fin N → ℝ) :
    actualUpperOccupancy η θ ∈ Icc 0 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := bump_population_bounds (fun j => upperPeriodicBump η (θ j))
    (fun j => upperPeriodicBump_bounds η (θ j))
  refine ⟨div_nonneg hp.1 hn.le, (div_le_one hn).mpr ?_⟩
  simpa only [Fintype.card_fin] using hp.2

theorem actualLowerOccupancy_mem_Icc {N : ℕ} (hN : 0 < N) (η : ℝ) (θ : Fin N → ℝ) :
    actualLowerOccupancy η θ ∈ Icc 0 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := bump_population_bounds (fun j => lowerPeriodicBump η (θ j))
    (fun j => lowerPeriodicBump_bounds η (θ j))
  refine ⟨div_nonneg hp.1 hn.le, (div_le_one hn).mpr ?_⟩
  simpa only [Fintype.card_fin] using hp.2

def fixedOccupancyAngle (η τ ρ υ θ : ℝ) : ℂ :=
  (θ : ℂ) - Complex.I * ((τ * (ρ * lowerPeriodicBump η θ - υ * upperPeriodicBump η θ) : ℝ) : ℂ)

theorem actualHomotopyAngle_eq_fixedOccupancy {N : ℕ} (η τ ξ : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) :
    actualHomotopyAngle η τ ξ θ i =
      fixedOccupancyAngle η (ξ * τ) (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) (θ i) := by
  simp only [actualHomotopyAngle, balancedHomotopyCoordinate, contourCoordinate,
    balancedShift, fixedOccupancyAngle, actualUpperOccupancy, actualLowerOccupancy,
    Fintype.card_fin]
  congr 2
  push_cast
  ring

theorem lower_branch_plateau_window (b η u : ℝ) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) (hu : |u| ≤ η) :
    upperPeriodicBump η (-b + u) = 0 ∧ lowerPeriodicBump η (-b + u) = 1 := by
  have hd := Real.abs_sin_sub_sin_le (b - u) b
  have hdist : |b - u - b| = |u| := by rw [show b - u - b = -u by ring, abs_neg]
  rw [hdist] at hd
  have hsin : 2 * η ≤ Real.sin (b - u) := by
    linarith [(abs_le.mp (hd.trans hu)).1]
  have hsneg : Real.sin (-b + u) = -Real.sin (b - u) := by
    rw [show -b + u = -(b - u) by ring, Real.sin_neg]
  refine ⟨upperPeriodicBump_zero hη (by rw [hsneg]; linarith), ?_⟩
  unfold lowerPeriodicBump
  rw [show -(-b + u) = b - u by ring]
  exact upperPeriodicBump_one hη hsin

theorem fixedOccupancyAngle_on_branch (b η τ ρ υ u : ℝ) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) (hu : |u| ≤ η) :
    fixedOccupancyAngle η τ ρ υ (-b + u) =
      ((-b + u : ℝ) : ℂ) - Complex.I * ((τ * ρ : ℝ) : ℂ) := by
  rcases lower_branch_plateau_window b η u hη hwidth hu with ⟨hp, hm⟩
  simp only [fixedOccupancyAngle, hp, hm, mul_one, mul_zero, sub_zero]

theorem actualCommonBranchDepth_mem_Icc {N : ℕ} (hN : 0 < N) (η τ ξ R : ℝ)
    (hτ : τ ∈ Icc 0 R) (hξ : ξ ∈ Icc 0 1) (θ : Fin N → ℝ) :
    ξ * τ * actualUpperOccupancy η θ ∈ Icc 0 R := by
  have hp := actualUpperOccupancy_mem_Icc hN η θ
  have hτξ : 0 ≤ ξ * τ := mul_nonneg hξ.1 hτ.1
  refine ⟨mul_nonneg hτξ hp.1, ?_⟩
  calc
    _ ≤ ξ * τ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp.2 hτξ
    _ ≤ τ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hξ.2 hτ.1
    _ ≤ R := hτ.2

theorem actualHomotopyRegular_branch_curve {N : ℕ} (α b ε η τ ξ : ℝ)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) (θ : Fin N → ℝ)
    (i : Fin N) (hi : |θ i + b| ≤ η) :
    (actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ).2 i =
      branchRegularCurve α b ε (ξ * τ * actualUpperOccupancy η θ) (θ i + b) := by
  change physicalRegularCoordinate (_, actualHomotopyAngle η τ ξ θ i) = _
  rw [actualHomotopyAngle_eq_fixedOccupancy]
  have ht : θ i = -b + (θ i + b) := by ring
  nth_rw 1 [ht]
  rw [fixedOccupancyAngle_on_branch b η (ξ * τ) _ _ (θ i + b) hη hwidth hi]
  rfl

/-- Sharp scale on the actual branch sector of the full balanced image.
All populations and every homotopy time are retained. The local interval
is derived from the full angular diameter and its actual mean. -/
theorem exists_actual_branch_shell_coordinate_difference (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ R C : ℝ, 0 < R ∧ R ≤ 1 ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ (ε : ℝ), 0 < ε → ε ≤ R →
      ∀ (η τ ξ : ℝ), 0 < η → 4 * η ≤ Real.sin b →
        τ ∈ Icc 0 R → ξ ∈ Icc 0 1 →
      ∀ (θ : Fin N → ℝ), ∀ r : ℝ, 0 < r →
        (∀ i j, |θ i - θ j| ≤ 2 * r) →
      ∀ i j : Fin N, |θ i + b| ≤ min R η → |θ j + b| ≤ min R η →
        ‖(actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ).2 i -
          (actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ).2 j‖ ≤
            C * r / Real.sqrt (|angularMean (fun k => θ k + b)| + r + ε) := by
  obtain ⟨R, C, hR, hR1, hC, hdiff⟩ :=
    exists_branch_coordinate_shell_difference α b hα hb hpoint
  refine ⟨R, C, hR, hR1, hC, ?_⟩
  intro N hN ε hε hεR η τ ξ hη hwidth hτ hξ θ r hr hdiam i j hi hj
  have hloc (k : Fin N) : θ k + b ∈
      Icc (angularMean (fun l => θ l + b) - 2 * r) (angularMean (fun l => θ l + b) + 2 * r) := by
    have hm := angularMean_distance_bound hN (fun l => θ l + b) (2 * r)
      (fun l m => by simpa only [add_sub_add_right_eq_sub] using hdiam l m) k
    exact ⟨by linarith [(abs_le.mp hm).1], by linarith [(abs_le.mp hm).2]⟩
  rw [actualHomotopyRegular_branch_curve α b ε η τ ξ hη hwidth θ i (hi.trans (min_le_right _ _)),
    actualHomotopyRegular_branch_curve α b ε η τ ξ hη hwidth θ j (hj.trans (min_le_right _ _))]
  exact hdiff ε hε hεR _ (actualCommonBranchDepth_mem_Icc hN η τ ξ R hτ hξ θ)
    _ r hr _ _ (hi.trans (min_le_left _ _)) (hj.trans (min_le_left _ _)) (hloc i) (hloc j)

end IsingBulk.AnisoF002.Isotropic
