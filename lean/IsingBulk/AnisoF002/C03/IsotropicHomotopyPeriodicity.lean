import IsingBulk.AnisoF002.C03.IsotropicActualHomotopyCurrent

/-!
# Periodic face matching for the actual balanced homotopy current

Every bump population, its derivative, the complete Jacobian and its
constructed inverse velocity are preserved by integral angular turns.
The eliminated last angle makes the two opposite faces differ by one
positive and one negative turn, so the original constrained current
has exact matching face values.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators Matrix
open Set Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def toroidalTranslation (k : ι → ℤ) (θ : ι → ℝ) : ι → ℝ :=
  fun i => θ i + (k i : ℝ) * (2 * Real.pi)

def complexToroidalTranslation (k : ι → ℤ) (w : ι → ℂ) : ι → ℂ :=
  fun i => w i + (k i : ℂ) * (2 * (Real.pi : ℂ))

def AngularPeriodic (F : (ι → ℂ) → ℂ) : Prop :=
  ∀ (k : ι → ℤ) (w : ι → ℂ), F (complexToroidalTranslation k w) = F w

omit [Fintype ι] [DecidableEq ι] in
theorem actual_bumps_toroidal (η : ℝ) (k : ι → ℤ) (θ : ι → ℝ) :
    (fun i => upperPeriodicBump η (toroidalTranslation k θ i)) =
      (fun i => upperPeriodicBump η (θ i)) ∧
    (fun i => lowerPeriodicBump η (toroidalTranslation k θ i)) =
      (fun i => lowerPeriodicBump η (θ i)) ∧
    (fun i => deriv (upperPeriodicBump η) (toroidalTranslation k θ i)) =
      (fun i => deriv (upperPeriodicBump η) (θ i)) ∧
    (fun i => deriv (lowerPeriodicBump η) (toroidalTranslation k θ i)) =
      (fun i => deriv (lowerPeriodicBump η) (θ i)) := by
  exact ⟨funext (fun i => (upperPeriodicBump_periodic η).int_mul (k i) (θ i)),
    funext (fun i => (lowerPeriodicBump_periodic η).int_mul (k i) (θ i)),
    funext (fun i => (periodic_deriv_F002 _ _ (upperPeriodicBump_periodic η)).int_mul (k i) (θ i)),
    funext (fun i => (periodic_deriv_F002 _ _ (lowerPeriodicBump_periodic η)).int_mul (k i) (θ i))⟩

omit [DecidableEq ι] in
theorem actualHomotopyDisplacement_toroidal (η τ : ℝ) (k : ι → ℤ) (θ : ι → ℝ) :
    actualHomotopyDisplacement η τ (toroidalTranslation k θ) =
      actualHomotopyDisplacement η τ θ := by
  obtain ⟨hp, hm, _, _⟩ := actual_bumps_toroidal η k θ
  unfold actualHomotopyDisplacement
  rw [hp, hm]

omit [DecidableEq ι] in
theorem actualHomotopyAngle_toroidal (η τ ξ : ℝ) (k : ι → ℤ) (θ : ι → ℝ) :
    actualHomotopyAngle η τ ξ (toroidalTranslation k θ) =
      complexToroidalTranslation k (actualHomotopyAngle η τ ξ θ) := by
  funext i
  simp only [actualHomotopyAngle_affine_time, actualHomotopyDisplacement_toroidal,
    complexToroidalTranslation, toroidalTranslation, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_intCast, Complex.ofReal_ofNat]
  ring

omit [DecidableEq ι] in
theorem actualBalancedJacobian_toroidal (η τ ξ : ℝ) (k : ι → ℤ) (θ : ι → ℝ) :
    actualBalancedJacobian η τ ξ (toroidalTranslation k θ) =
      actualBalancedJacobian η τ ξ θ := by
  obtain ⟨hp, hm, hdp, hdm⟩ := actual_bumps_toroidal η k θ
  unfold actualBalancedJacobian
  rw [hp, hm, hdp, hdm]

theorem actualHomotopyVelocity_toroidal (η τ ξ : ℝ) (k : ι → ℤ) (θ : ι → ℝ) (i : ι) :
    actualHomotopyVelocity η τ i (ξ, toroidalTranslation k θ) =
      actualHomotopyVelocity η τ i (ξ, θ) := by
  simp only [actualHomotopyVelocity, constructedAngularVelocity, homotopyCoordinate_matrix,
    homotopyCoordinate_timePartial, sub_zero, actualBalancedMatrix,
    actualBalancedJacobian_toroidal, actualHomotopyDisplacement_toroidal]

theorem homotopyPulledDensity_toroidal (η τ ξ : ℝ) (F : (ι → ℂ) → ℂ)
    (hF : AngularPeriodic F) (k : ι → ℤ) (θ : ι → ℝ) :
    homotopyPulledDensity η τ F (ξ, toroidalTranslation k θ) =
      homotopyPulledDensity η τ F (ξ, θ) := by
  rw [homotopyPulledDensity_actual, homotopyPulledDensity_actual,
    actualBalancedJacobian_toroidal, actualHomotopyAngle_toroidal, hF]

theorem homotopyCurrentFlux_toroidal (η τ ξ : ℝ) (F : (ι → ℂ) → ℂ)
    (hF : AngularPeriodic F) (k : ι → ℤ) (θ : ι → ℝ) (i : ι) :
    homotopyCurrentFlux η τ F i (ξ, toroidalTranslation k θ) =
      homotopyCurrentFlux η τ F i (ξ, θ) := by
  rw [homotopyCurrentFlux, homotopyCurrentFlux, actualHomotopyVelocity_toroidal,
    homotopyPulledDensity_toroidal η τ ξ F hF]

def constraintPeriodVector {n : ℕ} (i : Fin n) : Fin (n + 1) → ℤ :=
  Pi.single i.castSucc 1 - Pi.single (Fin.last n) 1

theorem affineConstraintAngles_period {n : ℕ} (a : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    affineConstraintAngles a (x + Pi.single i (2 * Real.pi)) =
      toroidalTranslation (constraintPeriodVector i) (affineConstraintAngles a x) := by
  rw [affineConstraintAngles_eq_snoc]
  funext j
  refine Fin.lastCases ?_ (fun l => ?_) j
  · simp [toroidalTranslation, constraintPeriodVector, affineConstraintAngles_eq_snoc,
      Finset.sum_add_distrib]
    ring
  · simp only [Fin.snoc_castSucc, Pi.add_apply, toroidalTranslation,
      affineConstraintAngles_eq_snoc, constraintPeriodVector, Pi.sub_apply]
    by_cases h : i = l
    · subst l
      simp
    · simp [Ne.symm h]

theorem constrained_homotopy_flux_periodic {n : ℕ} (η τ a ξ : ℝ)
    (F : (Fin (n + 1) → ℂ) → ℂ) (hF : AngularPeriodic F) (x : Fin n → ℝ) (i j : Fin n) :
    homotopyCurrentFlux η τ F j.castSucc (ξ, affineConstraintAngles a (x + Pi.single i (2 * Real.pi))) =
      homotopyCurrentFlux η τ F j.castSucc (ξ, affineConstraintAngles a x) := by
  rw [affineConstraintAngles_period, homotopyCurrentFlux_toroidal η τ ξ F hF]

end IsingBulk.AnisoF002.Isotropic
