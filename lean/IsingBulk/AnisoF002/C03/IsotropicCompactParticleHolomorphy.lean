import IsingBulk.AnisoF002.C03.IsotropicWeightedParticleHolomorphy

/-!
# Holomorphy and genuine derivatives of every compact right mean

The independent variables use ordinary Lebesgue measure. Compact support
reduces each affine lift to its actual finite box; centering is the same
Jacobian-one translation. No analytic continuation of a real cutoff is
used or needed.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory
open IsingBulk.AnisoF002.RegularTail.C03

def compactAffinePhysicalCoefficient (n : ℕ) (η τ ξ b δ ρ a : ℝ) (σ S : ℂ) : ℂ :=
  ∫ x : Fin n → ℝ, actualLowerCompactRightCutoff η b δ ρ (n + 1) (affineConstraintAngles a x) *
    homotopyPulledDensity η τ (isotropicBarePhysicalDensity S σ) (ξ, affineConstraintAngles a x)

def compactMeanPhysicalCoefficient (n : ℕ) (η τ ξ b δ ρ μ : ℝ) (σ S : ℂ) : ℂ :=
  ∫ x : Fin n → ℝ, actualLowerCompactRightCutoff η b δ ρ (n + 1) (centeredConstraintAngles μ x) *
    homotopyPulledDensity η τ (isotropicBarePhysicalDensity S σ) (ξ, centeredConstraintAngles μ x)

theorem compactAffinePhysicalCoefficient_eq_box {b δ ρ : ℝ} (hcut : RightCutoffGeometry b δ ρ)
    (n : ℕ) (η τ ξ a : ℝ) (σ S : ℂ) :
    compactAffinePhysicalCoefficient n η τ ξ b δ ρ a σ S =
      ∫ x in regularAngularBox n, actualLowerCompactRightCutoff η b δ ρ (n + 1) (affineConstraintAngles a x) *
        homotopyPulledDensity η τ (isotropicBarePhysicalDensity S σ) (ξ, affineConstraintAngles a x) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [actualLowerCompactRightCutoff, compactRightProduct_affine_zero_off_box hcut a x hx,
    mul_zero, zero_mul]

theorem compactMeanPhysicalCoefficient_eq_affine (n : ℕ) (η τ ξ b δ ρ μ : ℝ) (σ S : ℂ) :
    compactMeanPhysicalCoefficient n η τ ξ b δ ρ μ σ S =
      compactAffinePhysicalCoefficient n η τ ξ b δ ρ ((n + 1 : ℕ) * μ) σ S := by
  have hh := affineConstraint_integral_centered ((n + 1 : ℕ) * μ)
    (fun θ => actualLowerCompactRightCutoff η b δ ρ (n + 1) θ *
      homotopyPulledDensity η τ (isotropicBarePhysicalDensity S σ) (ξ, θ))
  have he : (((n + 1 : ℕ) : ℝ) * μ) / (n + 1 : ℕ) = μ := by field_simp
  rw [he] at hh
  exact hh.symm

theorem compactAffinePhysicalCoefficient_analyticAt {b δ ρ : ℝ} (hcut : RightCutoffGeometry b δ ρ)
    (n : ℕ) (η τ ξ a : ℝ) (σ : ℂ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (hσ : ‖σ‖ ≤ 1) (S : ℂ) (hS : 0 < S.im) :
    AnalyticAt ℂ (compactAffinePhysicalCoefficient n η τ ξ b δ ρ a σ) S := by
  let K := regularAngularBox n
  let H : (Fin n → ℝ) → ℂ × (Fin (n + 1) → ℂ) := fun x =>
    (actualLowerCompactRightCutoff η b δ ρ (n + 1) (affineConstraintAngles a x) *
      (actualBalancedJacobian η τ ξ (affineConstraintAngles a x)).det,
      actualHomotopyAngle η τ ξ (affineConstraintAngles a x))
  have hK : IsCompact K := isCompact_Icc
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hH : Continuous H := (((actualLowerCompactRightCutoff_contDiff η b δ ρ (n + 1) (k := 0)).continuous.mul
    (actualBalancedJacobian_det_continuous η τ ξ)).prodMk
      (actualHomotopyAngles_continuous η τ ξ)).comp (affineConstraintAngles_contDiff a 0).continuous
  have he : compactAffinePhysicalCoefficient n η τ ξ b δ ρ a σ =
      fun T => ∫ x, mixedPhysicalAnalyticFamily σ (T, H x) ∂volume.restrict K := by
    funext T
    rw [compactAffinePhysicalCoefficient_eq_box hcut]
    simp only [mixedPhysicalAnalyticFamily, H, K, homotopyPulledDensity_actual, mul_assoc]
  rw [he]
  apply analyticAt_integral_of_joint_analytic hK (ae_restrict_mem measurableSet_Icc) hH
  intro x _
  exact mixedPhysicalAnalyticFamily_analyticAt (by omega) hσ (S, H x)
    (fun i => actual_balanced_homotopy_sheet S hS η τ ξ hη hτ hξ (affineConstraintAngles a x) i)

theorem compactMeanPhysicalCoefficient_analyticAt {b δ ρ : ℝ} (hcut : RightCutoffGeometry b δ ρ)
    (n : ℕ) (η τ ξ μ : ℝ) (σ : ℂ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (hσ : ‖σ‖ ≤ 1) (S : ℂ) (hS : 0 < S.im) :
    AnalyticAt ℂ (compactMeanPhysicalCoefficient n η τ ξ b δ ρ μ σ) S := by
  have he := funext (fun T => compactMeanPhysicalCoefficient_eq_affine n η τ ξ b δ ρ μ σ T)
  rw [he]
  exact compactAffinePhysicalCoefficient_analyticAt hcut n η τ ξ _ σ hη hτ hξ hσ S hS

end IsingBulk.AnisoF002.Isotropic
