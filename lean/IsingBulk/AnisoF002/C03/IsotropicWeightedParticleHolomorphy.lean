import IsingBulk.AnisoF002.C03.IsotropicCompleteCompactPartition
import IsingBulk.AnisoF002.C03.RegularIsotropicMixedCoefficient
import IsingBulk.AnisoF002.C03.RegularCompactAnalytic

/-!
# Actual weighted particle holomorphy on the upper parameter half-plane

A real angular cutoff is carried as an independent scalar coordinate
of the analytic family. Thus only its genuine angular continuity is
used; no analytic extension of a smooth cutoff is assumed. The full
physical numerator, kernel and angular Jacobian remain literal.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory
open IsingBulk.AnisoF002.RegularTail.C03

theorem actualWeightedParticleIntegral_analyticAt {n : ℕ} (η τ ξ : ℝ) (σ : ℂ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hσ : ‖σ‖ ≤ 1)
    (g : (Fin (n + 1) → ℝ) → ℂ) (hg : Continuous g) (a : ℝ)
    (S : ℂ) (hS : 0 < S.im) :
    AnalyticAt ℂ (actualWeightedParticleIntegral η τ ξ σ g a) S := by
  let K := angularIntegrationBox n
  let H : (Fin n → ℝ) → ℂ × (Fin (n + 1) → ℂ) := fun x =>
    (g (affineConstraintAngles a x) * (actualBalancedJacobian η τ ξ (affineConstraintAngles a x)).det,
      actualHomotopyAngle η τ ξ (affineConstraintAngles a x))
  have hK : IsCompact K := isCompact_Icc
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hH : Continuous H := ((hg.mul (actualBalancedJacobian_det_continuous η τ ξ)).prodMk
    (actualHomotopyAngles_continuous η τ ξ)).comp (affineConstraintAngles_contDiff a 0).continuous
  have he : actualWeightedParticleIntegral η τ ξ σ g a =
      fun T => ∫ x, mixedPhysicalAnalyticFamily σ (T, H x) ∂volume.restrict K := by
    funext T
    simp only [actualWeightedParticleIntegral, mixedPhysicalAnalyticFamily, H, K,
      homotopyPulledDensity_actual, mul_assoc]
  rw [he]
  apply analyticAt_integral_of_joint_analytic hK (ae_restrict_mem measurableSet_Icc) hH
  intro x _
  exact mixedPhysicalAnalyticFamily_analyticAt (by omega) hσ (S, H x)
    (fun i => actual_balanced_homotopy_sheet S hS η τ ξ hη hτ hξ (affineConstraintAngles a x) i)

theorem actualWeightedParticleIntegral_iteratedDeriv {n : ℕ} (η τ ξ : ℝ) (σ : ℂ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (hσ : ‖σ‖ ≤ 1)
    (g : (Fin (n + 1) → ℝ) → ℂ) (hg : Continuous g) (a : ℝ)
    (S : ℂ) (hS : 0 < S.im) (j : ℕ) :
    iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ g a) S =
      ∫ x in angularIntegrationBox n, iteratedDeriv j (fun T => g (affineConstraintAngles a x) *
        homotopyPulledDensity η τ (isotropicBarePhysicalDensity T σ) (ξ, affineConstraintAngles a x)) S := by
  let K := angularIntegrationBox n
  let H : (Fin n → ℝ) → ℂ × (Fin (n + 1) → ℂ) := fun x =>
    (g (affineConstraintAngles a x) * (actualBalancedJacobian η τ ξ (affineConstraintAngles a x)).det,
      actualHomotopyAngle η τ ξ (affineConstraintAngles a x))
  have hK : IsCompact K := isCompact_Icc
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hH : Continuous H := ((hg.mul (actualBalancedJacobian_det_continuous η τ ξ)).prodMk
    (actualHomotopyAngles_continuous η τ ξ)).comp (affineConstraintAngles_contDiff a 0).continuous
  have hh := iteratedDeriv_integral_of_joint_analytic (μ := volume.restrict K)
    (f := mixedPhysicalAnalyticFamily σ)
    (g := H) hK (ae_restrict_mem measurableSet_Icc) hH
    (fun x _ => mixedPhysicalAnalyticFamily_analyticAt (by omega) hσ (S, H x)
      (fun i => actual_balanced_homotopy_sheet S hS η τ ξ hη hτ hξ (affineConstraintAngles a x) i)) j
  unfold actualWeightedParticleIntegral
  simpa only [mixedPhysicalAnalyticFamily, H, K,
    homotopyPulledDensity_actual, mul_assoc] using hh

theorem mixedPhysicalCoefficient_eq_weightedIntegral (n : ℕ) (η τ a : ℝ) (σ S : ℂ) :
    mixedPhysicalCoefficient n η τ a σ S =
      actualWeightedParticleIntegral (n := n) η τ 1 σ (fun θ => (mixedPopulationCutoff η θ : ℂ)) a S := by
  simp only [mixedPhysicalCoefficient, mixedPhysicalIntegrand, mixedAngularAmplitude,
    actualWeightedParticleIntegral, homotopyPulledDensity_actual, mul_assoc]

end IsingBulk.AnisoF002.Isotropic
