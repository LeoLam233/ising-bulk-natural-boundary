import IsingBulk.Anisotropic.NegativeCycles.WindingAngles
import IsingBulk.Anisotropic.RegularEdges.CenteredAngular

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open Set MeasureTheory
open scoped BigOperators

theorem coordinatePeriodic_shift {n : ℕ} {f : (Fin n→ℝ)→ℂ}
    (hp : CoordinatePeriodic n f) (c : Fin n→ℝ) :
    CoordinatePeriodic n (fun q => f (fun i => q i+c i)) := by
  intro q i
  have he : (fun j => Function.update q i (q i+2*Real.pi) j+c j)=
      Function.update (fun j => q j+c j) i (q i+c i+2*Real.pi) := by
    funext j
    by_cases hj : j=i
    · subst j
      simp only [Function.update_self]
      ring
    · simp [Function.update_of_ne hj]
  change f (fun j => Function.update q i (q i+2*Real.pi) j+c j)=_
  rw [he]
  exact hp (fun j => q j+c j) i

theorem angleBox_integral_eq_centered_shift (n : ℕ) (f : (Fin n→ℝ)→ℂ)
    (hc : Continuous f) (hp : CoordinatePeriodic n f) (c : Fin n→ℝ) :
    (∫q in angleBox n, f q)=∫v in Icc (fun _ => -Real.pi) (fun _ => Real.pi),
      f (fun i => v i+c i) := by
  rw [←angleBox_integral_shift n f hc hp c]
  exact angleBox_integral_eq_centered n _
    (hc.comp (continuous_pi (fun i => (continuous_apply i).add continuous_const)))
    (coordinatePeriodic_shift hp c)

theorem complexAngularDensity_winding (n : ℕ) (lam : ℝ) (z : ℂ) (d : ℝ) (k : ℤ)
    (hk : (n+1:ℕ)*(Real.pi+d)=(k:ℝ)*(2*Real.pi)) (v : Fin n→ℝ) :
    complexAngularDensity lam z (fun i => (physicalDependentAngles n (fun j => v j+Real.pi+d) i:ℂ))=
      complexAngularDensity lam z (fun i => ((Real.pi+d+shapeExtend v i:ℝ):ℂ)) := by
  rw [←complexAngularDensity_wrapAngle lam z,
    ←complexAngularDensity_wrapAngle lam z (fun i => Real.pi+d+shapeExtend v i)]
  congr 1
  funext i
  rw [physicalDependentAngles_winding n d k hk]

/-- Exact full-coefficient representation about a genuine winding center.
The transverse tuple is zero mean; its center is π+d, not π. -/
theorem unscaledAngularCoefficient_eq_winding (n : ℕ) {lam : ℝ} {z : ℂ}
    (hz : z∉spectralSet lam) (hS : spectralS z≠0) (d : ℝ) (k : ℤ)
    (hk : (n+1:ℕ)*(Real.pi+d)=(k:ℝ)*(2*Real.pi)) :
    unscaledAngularCoefficient n lam z=
      ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n *
        ∫v in Icc (fun _ : Fin n => -Real.pi) (fun _ => Real.pi),
          complexAngularDensity lam z (fun i => ((Real.pi+d+shapeExtend v i:ℝ):ℂ)) := by
  unfold unscaledAngularCoefficient
  rw [multiAngleIntegral_eq_box n _ (complexAngularDensity_dependent_continuous n hz hS),
    angleBox_integral_eq_centered_shift n _ (complexAngularDensity_dependent_continuous n hz hS)
      (complexAngularDensity_dependent_periodic n lam z) (fun _ => Real.pi+d)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro v _
  simpa only [add_assoc] using complexAngularDensity_winding n lam z d k hk v

end IsingBulk.Anisotropic.NegativeCycles
