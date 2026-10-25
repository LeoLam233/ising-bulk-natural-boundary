import IsingBulk.Joint.RegularEdges.PhysicalAngular
import IsingBulk.Joint.RegularEdges.AngularCoefficient
import IsingBulk.Anisotropic.RegularEdges.CenteredAngular

/-! # Exact physical-to-normal-form angular identities
All functions are evaluated at the actual independent coupling point. No
fixed-ratio representation or constant-anisotropy assumption is introduced.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.HT.Contour Set MeasureTheory
open IsingBulk.Anisotropic.RegularEdges
open scoped BigOperators

@[simp] theorem physicalRoot_wrapAngle (K : Coupling) (q : ℝ) :
    Negative.transferRoot K (wrapAngle q:ℂ)=Negative.transferRoot K (q:ℂ) := by
  simp only [Negative.transferRoot,Negative.transferW,←Complex.ofReal_cos,cos_wrapAngle]

theorem physicalDensity_wrapAngle {N : ℕ} (K : Coupling) (q : Fin N → ℝ) :
    Negative.complexAngularDensity K (fun i => (wrapAngle (q i):ℂ))=
      Negative.complexAngularDensity K (fun i => (q i:ℂ)) := by
  simp only [Negative.complexAngularDensity,Negative.complexAngularWeight,
    physicalRoot_wrapAngle,angularRootPair_wrapAngle]

theorem physicalDensity_dependent_periodic (n : ℕ) (K : Coupling) :
    CoordinatePeriodic n (fun q => Negative.complexAngularDensity K
      (fun i => (physicalDependentAngles n q i:ℂ))) := by
  intro q i
  dsimp only
  rw [←physicalDensity_wrapAngle K
    (physicalDependentAngles n (Function.update q i (q i+2*Real.pi))),
    ←physicalDensity_wrapAngle K (physicalDependentAngles n q)]
  congr 1
  funext j
  rw [wrappedDependentAngles_update]

theorem physicalDensity_dependent_continuous (n : ℕ) {K : Coupling}
    (hK : K∉spectralSet) (hS : S K≠0) :
    Continuous (fun q : Fin n → ℝ => Negative.complexAngularDensity K
      (fun i => (physicalDependentAngles n q i:ℂ))) := by
  have hp : Continuous (fun q : Fin n → ℝ => fun i => (physicalDependentAngles n q i:ℂ)) :=
    continuous_pi (fun i => Complex.continuous_ofReal.comp
      ((continuous_apply i).comp (physicalDependentAngles_continuous n)))
  apply continuous_iff_continuousAt.mpr
  intro q
  exact (Negative.complexAngularDensity_joint_analyticAt (by omega) hK hS
    (physicalDependentAngles n q)).continuousAt.comp
      (f := fun q => (K,fun i => (physicalDependentAngles n q i:ℂ)))
      (continuous_const.prodMk hp).continuousAt

theorem physicalAngular_eq_centered (n : ℕ) {K : Coupling}
    (hK : K∉spectralSet) (hS : S K≠0) :
    Negative.unscaledAngularCoefficient n K = edgeCoefficientNormalization n *
      ∫ q in edgeCenteredCube n, Negative.complexAngularDensity K
        (fun i => ((shapeExtend q i:ℝ):ℂ)) := by
  unfold Negative.unscaledAngularCoefficient
  rw [multiAngleIntegral_eq_box n _ (physicalDensity_dependent_continuous n hK hS),
    angleBox_integral_eq_centered n _ (physicalDensity_dependent_continuous n hK hS)
      (physicalDensity_dependent_periodic n K)]
  rfl

theorem physicalRoot_eq_positiveRoot {b : ℝ} {curve : ℂ → Coupling} {u : ℂ}
    (he : Transverse.positiveParameter b (curve u)=u)
    (hu : 0<u.im) (hB : 0<(Transverse.curveB curve u).im) (q : ℝ) :
    Negative.transferRoot (curve u) (q:ℂ)=edgeParamRoot b (Transverse.curveB curve) u q := by
  unfold Negative.transferRoot edgeParamRoot
  rw [Negative.transferW_eq,Transverse.positive_dispersion_identity b curve u (q:ℂ) he]
  rw [←Complex.ofReal_cos]
  apply smallRoot_eq_continuedRoot
  exact Transverse.dispersion_im_pos hu hB q

/-- The complete angular density, including `(1+Z)/(1-Z)`, is identified. -/
theorem physicalDensity_eq_positiveDensity {N : ℕ} {b : ℝ}
    {curve : ℂ → Coupling} {u : ℂ}
    (he : Transverse.positiveParameter b (curve u)=u)
    (hu : 0<u.im) (hB : 0<(Transverse.curveB curve u).im) (q : Fin N → ℝ) :
    Negative.complexAngularDensity (curve u) (fun i => (q i:ℂ))=
      edgeAngularDensity b (Transverse.curveB curve) (Transverse.curveS curve) u q := by
  unfold Negative.complexAngularDensity Negative.complexAngularWeight edgeAngularDensity edgeAngularWeight
  simp_rw [physicalRoot_eq_positiveRoot he hu hB]
  simp [firstStrictPairs,Finset.prod_filter,Fintype.prod_prod_type,edgeRootProduct,
    Transverse.curveB,Transverse.curveS,transferB]

theorem physicalAngular_eq_positiveCoefficient (n : ℕ) {b : ℝ}
    {curve : ℂ → Coupling} {u : ℂ}
    (hK : curve u∉spectralSet) (hS : S (curve u)≠0)
    (he : Transverse.positiveParameter b (curve u)=u)
    (hu : 0<u.im) (hB : 0<(Transverse.curveB curve u).im) :
    Negative.unscaledAngularCoefficient n (curve u)=
      angularCoefficient n b (Transverse.curveB curve) (Transverse.curveS curve) u := by
  rw [physicalAngular_eq_centered n hK hS]
  simp_rw [physicalDensity_eq_positiveDensity he hu hB]
  rfl

end
end IsingBulk.Joint.RegularEdges
