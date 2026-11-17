import IsingBulk.AnisoF002.C03.IsotropicConstrainedPhasePath

/-!
# Regularity of the actual coarea integrand on a constrained fiber

The full balanced populations remain functions of every real angle.
The canonical physical sheet makes the actual phase and Jacobian
smooth on each entire real constraint line at positive radial depth.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem actualPhysicalPhase_angles_contDiff {N : ℕ} (s : ℂ) (hs : 0 < s.im)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (i : Fin N) (n : ℕ∞) :
    ContDiff ℝ n (fun θ : Fin N → ℝ => actualPhysicalPhase η τ ξ (s, θ) i) := by
  have he : (fun θ : Fin N → ℝ => actualPhysicalPhase η τ ξ (s, θ) i) =
      (fun θ => actualPhysicalCoordinate η τ ξ i (s, θ) - actualHomotopyAngle η τ ξ θ i) := by
    funext θ
    simp only [actualPhysicalPhase, actualPhysicalCoordinate, physicalRegularCoordinate,
      add_sub_cancel_left]
  rw [he]
  refine ContDiff.sub ?_ (actualHomotopyAngle_contDiff η τ ξ i n)
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  exact (actualPhysicalCoordinate_contDiffAt η τ ξ i (s, θ) n
    (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ hξ θ i)).comp θ
      (contDiffAt_const.prodMk contDiffAt_id)

theorem actualTotalPhase_angles_contDiff {N : ℕ} (s : ℂ) (hs : 0 < s.im)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (n : ℕ∞) :
    ContDiff ℝ n (fun θ : Fin N → ℝ => actualTotalPhase η τ ξ (s, θ)) :=
  ContDiff.sum (fun i _ => actualPhysicalPhase_angles_contDiff s hs η τ ξ hη hτ hξ i n)

theorem constrainedAngleLine_contDiff {N : ℕ} (θ : Fin N → ℝ) (i j : Fin N) (n : ℕ∞) :
    ContDiff ℝ n (constrainedAngleLine θ i j) := by
  unfold constrainedAngleLine
  exact contDiff_const.add (contDiff_id.smul contDiff_const)

theorem actualTotalPhase_constrainedLine_contDiff {N : ℕ} (s : ℂ) (hs : 0 < s.im)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (θ : Fin N → ℝ) (i j : Fin N) (n : ℕ∞) :
    ContDiff ℝ n (fun t : ℝ => actualTotalPhase η τ ξ (s, constrainedAngleLine θ i j t)) :=
  (actualTotalPhase_angles_contDiff s hs η τ ξ hη hτ hξ n).comp
    (constrainedAngleLine_contDiff θ i j n)

theorem actualPhaseSlope_angles_continuous {N : ℕ} (s : ℂ) (hs : 0 < s.im)
    (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ) (i : Fin N) :
    Continuous (fun θ : Fin N → ℝ => actualPhaseSlope s η τ ξ θ i) := by
  have hw := (actualHomotopyAngle_contDiff η τ ξ i 0).continuous
  have hφ := (actualPhysicalPhase_angles_contDiff s hs η τ ξ hη hτ hξ i 0).continuous
  exact (Complex.continuous_sin.comp hw).neg.div (Complex.continuous_sin.comp hφ)
    (fun θ => upperPhysicalPhase_sin_ne_zero _
      (actual_balanced_homotopy_sheet s hs η τ ξ hη hτ hξ θ i))

theorem actualProjectedPhase_constrainedLine_derivative_continuous {N : ℕ}
    (s : ℂ) (hs : 0 < s.im) (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    Continuous (fun t : ℝ => (frozenObliqueRotation *
      (actualFullPhaseDerivative s η τ ξ (constrainedAngleLine θ i j t) i -
        actualFullPhaseDerivative s η τ ξ (constrainedAngleLine θ i j t) j)).re) := by
  let ν : ℝ → ℝ := fun t =>
    (frozenObliqueRotation * actualTotalPhase η τ ξ (s, constrainedAngleLine θ i j t)).re
  have hν : ContDiff ℝ 2 ν := Complex.reCLM.contDiff.comp
    (contDiff_const.mul (actualTotalPhase_constrainedLine_contDiff s hs η τ ξ hη hτ hξ θ i j 2))
  have he : deriv ν = (fun t : ℝ => (frozenObliqueRotation *
      (actualFullPhaseDerivative s η τ ξ (constrainedAngleLine θ i j t) i -
        actualFullPhaseDerivative s η τ ξ (constrainedAngleLine θ i j t) j)).re) := by
    funext t
    exact (actualProjectedPhase_constrainedLine_hasDerivAt s hs η τ ξ hη hτ hξ θ i j t).deriv
  rw [← he]
  exact (show ContDiff ℝ 1 (deriv ν) from hν.deriv').continuous

theorem actualExtremeJacobian_constrainedLine_continuous {N : ℕ}
    (s : ℂ) (hs : 0 < s.im) (η τ ξ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hξ : 0 ≤ ξ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    Continuous (fun t : ℝ =>
      ‖(1 + actualPhaseSlope s η τ ξ (constrainedAngleLine θ i j t) i) *
        (1 + actualPhaseSlope s η τ ξ (constrainedAngleLine θ i j t) j)‖) := by
  have hp := (constrainedAngleLine_contDiff θ i j 0).continuous
  exact ((continuous_const.add ((actualPhaseSlope_angles_continuous s hs η τ ξ hη hτ hξ i).comp hp)).mul
    (continuous_const.add ((actualPhaseSlope_angles_continuous s hs η τ ξ hη hτ hξ j).comp hp))).norm

end IsingBulk.AnisoF002.Isotropic
