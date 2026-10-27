import IsingBulk.Preferred22.ContourDeformation
import IsingBulk.Preferred22.AngularAnalytic

/-! Exact identification of the contour density with the common literal
complex angular density used by the Preferred22 analytic modules. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
open MeasureTheory

theorem rootFreeDensity_eq_complexAngularDensity {N : ℕ}
    (s : ℂ) (w : Fin N → ℂ) :
    rootFreeDensity s (fun i => Complex.exp (Complex.I*w i)) =
      complexAngularDensity (s,w) := by
  have he : contourRoots s (fun i => Complex.exp (Complex.I*w i)) =
      complexAngularRoots (s,w) := by
    funext i
    simp only [contourRoots, complexAngularRoots, complexW_exp_I]
  simp only [rootFreeDensity, complexAngularDensity, complexAngleRoot, he]

theorem deformedCoefficient_density_formula (n : ℕ) (s : ℂ) (τ : ℝ) (p m : ℝ → ℝ) :
    deformedCoefficient n s τ 1 p m =
      ((Nat.factorial (n+1):ℂ)*(2*Real.pi:ℂ)^n)⁻¹ *
        ∫ θ in angularBox n,
          complexAngularDensity (s,deformedAngles τ p m (constrainedAngles θ)) *
            (constrainedAngularJacobian τ 1 p m θ).det := by
  unfold deformedCoefficient
  congr 1
  apply MeasureTheory.setIntegral_congr_fun
  · exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  · intro θ _
    dsimp only
    have he : homotopyRoot τ 1 p m (constrainedAngles θ) =
        fun i => Complex.exp (Complex.I*deformedAngles τ p m (constrainedAngles θ) i) := by
      funext i
      exact homotopyRoot_eq_exp_deformedAngles τ p m (constrainedAngles θ) i
    rw [he, rootFreeDensity_eq_complexAngularDensity]

end
end IsingBulk.Preferred22
