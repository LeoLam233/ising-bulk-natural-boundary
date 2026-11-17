import IsingBulk.AnisoF002.C03.IsotropicWholeArcDerivative
import IsingBulk.AnisoF002.C03.IsotropicPhaseTransport

/-!
# The physical phase derivative with all actual occupancy terms

The phase is the actual canonical phase. Its full coordinate derivative
is obtained by differentiating the original balanced contour before
regrouping either global population. These are the terms needed for
the constrained extreme-coordinate coarea derivative.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def physicalPhaseAngleSlope (s w : ℂ) : ℂ :=
  -Complex.sin w / Complex.sin (upperPhysicalPhase (isotropicDispersion (s, w)))

theorem physicalPhaseAngle_hasDerivAt (s w : ℂ)
    (hW : 0 < (isotropicDispersion (s, w)).im) :
    HasDerivAt (fun z => upperPhysicalPhase (isotropicDispersion (s, z)))
      (physicalPhaseAngleSlope s w) w := by
  have hd := (upperPhysicalPhase_hasDerivAt _ hW).comp w
    ((hasDerivAt_const w s).sub (Complex.hasDerivAt_cos w))
  convert hd using 1
  · rfl
  · unfold physicalPhaseAngleSlope
    ring

def actualPhaseSlope {N : ℕ} (s : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  physicalPhaseAngleSlope s (actualHomotopyAngle η τ ξ θ i)

def actualLowerPhasePopulation {N : ℕ} (s : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) : ℂ :=
  ∑ j, (lowerPeriodicBump η (θ j) : ℂ) * actualPhaseSlope s η τ ξ θ j

def actualUpperPhasePopulation {N : ℕ} (s : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) : ℂ :=
  ∑ j, (upperPeriodicBump η (θ j) : ℂ) * actualPhaseSlope s η τ ξ θ j

def actualOccupancyPhaseCorrection {N : ℕ} (s : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  -Complex.I * (((ξ * τ) / (N : ℝ) : ℝ) : ℂ) * ((deriv (upperPeriodicBump η) (θ i) : ℝ) : ℂ) *
      actualLowerPhasePopulation s η τ ξ θ +
    Complex.I * (((ξ * τ) / (N : ℝ) : ℝ) : ℂ) * ((deriv (lowerPeriodicBump η) (θ i) : ℝ) : ℂ) *
      actualUpperPhasePopulation s η τ ξ θ

/-- Frozen F002 `eq:iso-occupancy-derivative` for the actual physical
phase, including both global population derivatives. -/
theorem actualTotalPhase_coordinateLine_hasDerivAt {N : ℕ} (s : ℂ) (hs : 0 < s.im)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (θ : Fin N → ℝ) (i : Fin N) :
    HasDerivAt (fun t : ℝ => actualTotalPhase η τ ξ (s, coordinateLine θ i t))
      (actualPhaseSlope s η τ ξ θ i *
          fixedOccupancySlope η (ξ * τ) (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) (θ i) +
        actualOccupancyPhaseCorrection s η τ ξ θ i) 0 := by
  have hscale : ξ * (τ / (N : ℝ)) = (ξ * τ) / N := by ring
  have hφ (j : Fin N) : HasDerivAt (fun z => upperPhysicalPhase (isotropicDispersion (s, z)))
      (actualPhaseSlope s η τ ξ θ j)
      (contourCoordinate θ (balancedShift ((ξ * τ) / (N : ℝ))
        (fun l => upperPeriodicBump η (θ l)) (fun l => lowerPeriodicBump η (θ l))) j) := by
    have hh := physicalPhaseAngle_hasDerivAt s (actualHomotopyAngle η τ ξ θ j)
      (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ hξ θ j)
    simpa only [actualPhaseSlope, actualHomotopyAngle, balancedHomotopyCoordinate,
      Fintype.card_fin, hscale] using hh
  have hh := deformedOccupancy_hasDerivAt ((ξ * τ) / (N : ℝ)) θ i
    (upperPeriodicBump η) (lowerPeriodicBump η)
    (deriv (upperPeriodicBump η) (θ i)) (deriv (lowerPeriodicBump η) (θ i))
    (fun z => upperPhysicalPhase (isotropicDispersion (s, z))) (actualPhaseSlope s η τ ξ θ)
    ((upperPeriodicBump_contDiff η (n := 1)).differentiable_one (θ i)).hasDerivAt
    ((lowerPeriodicBump_contDiff η (n := 1)).differentiable_one (θ i)).hasDerivAt hφ
  have hefun : deformedOccupancy ((ξ * τ) / (N : ℝ)) θ i (upperPeriodicBump η) (lowerPeriodicBump η)
      (fun z => upperPhysicalPhase (isotropicDispersion (s, z))) =
      (fun t : ℝ => actualTotalPhase η τ ξ (s, coordinateLine θ i t)) := by
    funext t
    simp only [deformedOccupancy, actualTotalPhase, actualPhysicalPhase,
      actualHomotopyAngle, balancedHomotopyCoordinate, balancedContourPath, Fintype.card_fin, hscale]
  rw [hefun] at hh
  apply hh.congr_deriv
  simp only [fixedOccupancySlope, actualUpperOccupancy, actualLowerOccupancy,
    actualOccupancyPhaseCorrection, actualLowerPhasePopulation, actualUpperPhasePopulation]
  push_cast
  ring

theorem actual_bump_derivative_lipschitz (η : ℝ) :
    ∃ L : ℝ, 0 < L ∧
      (∀ x y, |deriv (upperPeriodicBump η) x - deriv (upperPeriodicBump η) y| ≤ L * |x - y|) ∧
      (∀ x y, |deriv (lowerPeriodicBump η) x - deriv (lowerPeriodicBump η) y| ≤ L * |x - y|) := by
  have hper : 2 * Real.pi ≠ 0 := ne_of_gt (mul_pos (by norm_num) Real.pi_pos)
  have hp : ContDiff ℝ 1 (deriv (upperPeriodicBump η)) :=
    (upperPeriodicBump_contDiff η (n := 2)).deriv'
  have hm : ContDiff ℝ 1 (deriv (lowerPeriodicBump η)) :=
    (lowerPeriodicBump_contDiff η (n := 2)).deriv'
  obtain ⟨Lp, hLp, _, hpL⟩ := periodic_C1_deriv_bound_F002 (deriv (upperPeriodicBump η)) _ hper
    (periodic_deriv_F002 _ _ (upperPeriodicBump_periodic η)) hp
  obtain ⟨Lm, _, _, hmL⟩ := periodic_C1_deriv_bound_F002 (deriv (lowerPeriodicBump η)) _ hper
    (periodic_deriv_F002 _ _ (lowerPeriodicBump_periodic η)) hm
  refine ⟨max Lp Lm, hLp.trans_le (le_max_left _ _), ?_, ?_⟩
  · intro x y
    exact (hpL x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
  · intro x y
    exact (hmL x y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))

theorem actualPhasePopulation_norm_bounds {N : ℕ} (s : ℂ) (η τ ξ Q : ℝ)
    (θ : Fin N → ℝ) (hψ : ∀ i, ‖actualPhaseSlope s η τ ξ θ i‖ ≤ Q) :
    ‖actualLowerPhasePopulation s η τ ξ θ‖ ≤ (N : ℝ) * Q ∧
      ‖actualUpperPhasePopulation s η τ ξ θ‖ ≤ (N : ℝ) * Q := by
  have hg (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
      ‖∑ j, (p j : ℂ) * actualPhaseSlope s η τ ξ θ j‖ ≤ (N : ℝ) * Q := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : Fin N, Q := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp j).1]
        exact (mul_le_mul (hp j).2 (hψ j) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul Q)
      _ = _ := by simp
  exact ⟨hg _ (fun i => lowerPeriodicBump_bounds η (θ i)), hg _ (fun i => upperPeriodicBump_bounds η (θ i))⟩

end IsingBulk.AnisoF002.Isotropic
