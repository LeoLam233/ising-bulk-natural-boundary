import IsingBulk.Joint.Geometry.TransferChart
import IsingBulk.Joint.RegularEdges.NormalFormIdentity
import IsingBulk.Joint.RegularEdges.WeightedFullSum
import IsingBulk.Anisotropic.RegularEdges.EvenPiShift
import IsingBulk.Anisotropic.RegularEdges.EvenModelPhase

/-! # Negative endpoint: exact even-parity transport
The pi translation and its particle-number sign are retained exactly. Odd
negative edges require the separate all-winding argument and are not inferred.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section

def negativeParameter (b : ℂ) (K : Coupling) : ℂ := transferC K+transferB K-b
def negativeCurveB (curve : ℂ → Coupling) (u : ℂ) : ℂ := -transferB (curve u)

theorem negativeParameter_analyticAt {curve : ℂ → Coupling} {u : ℂ}
    (b : ℂ) (hc : AnalyticAt ℂ curve u) (hS : S (curve u)≠0) :
    AnalyticAt ℂ (fun t => negativeParameter b (curve t)) u :=
  (((transferC_analyticAt hS).comp hc).add ((transferB_analyticAt hS).comp hc)).sub analyticAt_const

theorem negativeCurveB_analyticAt {curve : ℂ → Coupling} {u : ℂ}
    (hc : AnalyticAt ℂ curve u) (hS : S (curve u)≠0) :
    AnalyticAt ℂ (negativeCurveB curve) u := (curveB_analyticAt hc hS).neg

end
end IsingBulk.Joint.Transverse

namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.HT.Contour Set MeasureTheory
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
open scoped BigOperators

theorem physicalRoot_eq_negativeRoot {b : ℝ} {curve : ℂ → Coupling} {u : ℂ}
    (he : Transverse.negativeParameter b (curve u)=u)
    (hu : 0<u.im) (hB : 0<(Transverse.negativeCurveB curve u).im) (q : ℝ) :
    Negative.transferRoot (curve u) (q:ℂ)=edgeParamRoot b (Transverse.negativeCurveB curve) u (q-Real.pi) := by
  have hw : Negative.transferW (curve u) (q:ℂ)=
      edgeParamW b (Transverse.negativeCurveB curve) u (q-Real.pi) := by
    rw [Negative.transferW_eq]
    unfold edgeParamW Transverse.negativeCurveB
    rw [Real.cos_sub_pi,Complex.ofReal_neg,Complex.ofReal_cos]
    unfold Transverse.negativeParameter at he
    linear_combination he
  unfold Negative.transferRoot edgeParamRoot
  rw [hw]
  apply smallRoot_eq_continuedRoot
  exact Transverse.dispersion_im_pos hu hB (q-Real.pi)

theorem physicalWeight_eq_negativeWeight {N : ℕ} {b : ℝ}
    {curve : ℂ → Coupling} {u : ℂ}
    (he : Transverse.negativeParameter b (curve u)=u)
    (hu : 0<u.im) (hB : 0<(Transverse.negativeCurveB curve u).im) (q : Fin N → ℝ) :
    Negative.complexAngularWeight (curve u) (fun i => (q i:ℂ))=
      (-1:ℂ)^(N.choose 2)*edgeAngularWeight b
        (Transverse.negativeCurveB curve) (Transverse.curveS curve) u (fun i => q i-Real.pi) := by
  rw [edgeAngularWeight_eq_edgeNumerator,edgeNumerator_eq_indexed]
  unfold Negative.complexAngularWeight
  simp_rw [physicalRoot_eq_negativeRoot he hu hB,angularRootPair_shift_pi]
  have hcoef : (T (curve u)/S (curve u))^(N.choose 2)=
      (-1:ℂ)^(N.choose 2)*(Transverse.negativeCurveB curve u)^(N.choose 2) := by
    rw [←mul_pow]
    congr 1
    dsimp [Transverse.negativeCurveB,transferB]
    ring
  rw [hcoef]
  dsimp [Transverse.curveS]
  ring

theorem physicalDensity_eq_negativeDensity {N : ℕ} {b : ℝ}
    {curve : ℂ → Coupling} {u : ℂ}
    (he : Transverse.negativeParameter b (curve u)=u)
    (hu : 0<u.im) (hB : 0<(Transverse.negativeCurveB curve u).im) (q : Fin N → ℝ) :
    Negative.complexAngularDensity (curve u) (fun i => (q i:ℂ))=
      (-1:ℂ)^(N.choose 2)*edgeAngularDensity b
        (Transverse.negativeCurveB curve) (Transverse.curveS curve) u (fun i => q i-Real.pi) := by
  unfold Negative.complexAngularDensity edgeAngularDensity edgeRootProduct
  rw [physicalWeight_eq_negativeWeight he hu hB]
  simp_rw [physicalRoot_eq_negativeRoot he hu hB]
  ring

theorem physicalDensity_negative_even_shift {n : ℕ} (hn : Even (n+1)) {b : ℝ}
    {curve : ℂ → Coupling} {u : ℂ}
    (he : Transverse.negativeParameter b (curve u)=u)
    (hu : 0<u.im) (hB : 0<(Transverse.negativeCurveB curve u).im) (q : Fin n → ℝ) :
    Negative.complexAngularDensity (curve u)
      (fun i => (physicalDependentAngles n (fun j => q j+Real.pi) i:ℂ))=
      (-1:ℂ)^((n+1).choose 2)*edgeAngularDensity b
        (Transverse.negativeCurveB curve) (Transverse.curveS curve) u (physicalDependentAngles n q) := by
  rw [physicalDensity_eq_negativeDensity he hu hB]
  congr 1
  rw [←edgeAngularDensity_wrapAngle b (Transverse.negativeCurveB curve) (Transverse.curveS curve) u
    (fun i => physicalDependentAngles n (fun j => q j+Real.pi) i-Real.pi),
    ←edgeAngularDensity_wrapAngle b (Transverse.negativeCurveB curve) (Transverse.curveS curve) u
      (physicalDependentAngles n q)]
  congr 1
  funext i
  exact even_dependent_pi_shift_wrap hn q i

theorem physicalAngular_eq_negative_even {n : ℕ} (hn : Even (n+1)) {b : ℝ}
    {curve : ℂ → Coupling} {u : ℂ}
    (hK : curve u∉spectralSet) (hS : S (curve u)≠0)
    (he : Transverse.negativeParameter b (curve u)=u)
    (hu : 0<u.im) (hB : 0<(Transverse.negativeCurveB curve u).im) :
    Negative.unscaledAngularCoefficient n (curve u)=(-1:ℂ)^((n+1).choose 2)*
      angularCoefficient n b (Transverse.negativeCurveB curve) (Transverse.curveS curve) u := by
  unfold Negative.unscaledAngularCoefficient
  rw [multiAngleIntegral_eq_box n _ (physicalDensity_dependent_continuous n hK hS),
    angleBox_integral_eq_centered_pi_shift]
  simp_rw [physicalDensity_negative_even_shift hn he hu hB]
  rw [integral_const_mul]
  dsimp [angularCoefficient,edgeCoefficientNormalization,edgeCenteredCube]
  change _ = (-1:ℂ)^((n+1).choose 2) *
    (((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n *
      ∫ q in Icc (fun _ : Fin n => -Real.pi) (fun _ => Real.pi),
        edgeAngularDensity b (Transverse.negativeCurveB curve) (Transverse.curveS curve) u
          (physicalDependentAngles n q))
  ring


/-- The even pi-shift sign is exactly the scale `S ↦ iS`, not an omitted
particle-dependent phase. -/
theorem physicalAngular_eq_negative_even_model {n : ℕ} (hn : Even (n+1)) {b : ℝ}
    {curve : ℂ → Coupling} {u : ℂ}
    (hK : curve u∉spectralSet) (hS : S (curve u)≠0)
    (he : Transverse.negativeParameter b (curve u)=u)
    (hu : 0<u.im) (hB : 0<(Transverse.negativeCurveB curve u).im) :
    Negative.unscaledAngularCoefficient n (curve u)=
      angularCoefficient n b (Transverse.negativeCurveB curve)
        (fun v => Complex.I*Transverse.curveS curve v) u := by
  rw [physicalAngular_eq_negative_even hn hK hS he hu hB,even_pair_phase_eq_I_inv_pow hn]
  unfold angularCoefficient
  simp_rw [edgeAngularDensity_I_scale,integral_const_mul]
  ring

end
end IsingBulk.Joint.RegularEdges
