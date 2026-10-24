import IsingBulk.Anisotropic.Controls.Nonvacuity
import IsingBulk.Anisotropic.Final.Target

namespace IsingBulk.Anisotropic.Controls
noncomputable section
open FormFactors

/-- Zero coupling cannot be silently admitted by the physical-response theorem:
Lean's totalized division then makes the beta-normalized observable constant. -/
theorem zero_coupling_not_low_physical_boundary {lam : ℝ} (hlam : 0<lam) :
    ¬NaturalBoundaryOn (omegaL lam) (lowPhysicalBulk 0 lam) := by
  have he : lowPhysicalBulk 0 lam=(fun _ => (0:ℂ)) := by
    funext z
    simp [lowPhysicalBulk,inverseTemperature]
  rw [he]
  exact constant_not_low_natural_boundary hlam 0

/-- A synthetic one-site covariance checks that the LT vacuum subtraction is
inside the whole-lattice sum. This is a definition control, not a Gibbs model. -/
theorem connected_subtraction_inside_tsum (lam x : ℝ) :
    lowCovarianceSum lam (fun y v => realMagnetizationSq lam y+
      if v=(0,0) then 1 else 0) x=1 := by
  classical
  simp only [lowCovarianceSum,add_sub_cancel_left]
  simp

/-- The energy-field convention retains exactly beta=x/(2J), not x/J. -/
theorem real_response_beta_factor (J lam x : ℝ) (corr : ℝ → LatticeSite → ℝ) :
    lowEnergyFieldResponse J lam corr x=(x/(2*J))*lowCovarianceSum lam corr x := rfl

end
end IsingBulk.Anisotropic.Controls
