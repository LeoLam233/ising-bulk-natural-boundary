import IsingBulk.Anisotropic.NegativeNormalForm.WeightedRadialBeta
import IsingBulk.Anisotropic.NegativeNormalForm.BetaTruncatedError
import IsingBulk.Anisotropic.NegativeDominance.ConstrainedBetaKernel

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set IsingBulk.First IsingBulk.Anisotropic.NegativeDominance
open scoped BigOperators

theorem weightedShapeBeta_radial {n : ℕ} (hn : 1≤n) (j : ℕ) (tau c : ℝ) (w : ℝ → ℝ) :
    (∫ q : Fin n → ℝ, w (c*(∑ i : Fin (n+1),shapeExtend q i^2)/tau)*
      constrainedBetaKernel n j tau c q)=shapeAngularConstant n*
        (∫ r in Ioi (0:ℝ),r^(n-1+(n+1)*n)*w (c*r^2/tau)/(tau+c*r^2)^(j+1)) := by
  have hpolar := integral_shapeVandermonde_polar hn
    (fun r => ((w (c*r^2/tau)/(tau+c*r^2)^(j+1):ℝ):ℂ))
  have hfree := integral_shapeExtend n
    (fun x => (shapeVandermondeSq x:ℂ)*((w (c*‖x‖^2/tau)/(tau+c*‖x‖^2)^(j+1):ℝ):ℂ))
  simp only [Complex.real_smul] at hpolar
  rw [hpolar] at hfree
  simp only [←Complex.ofReal_mul,integral_complex_ofReal] at hfree
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul]
  convert hfree using 1
  · congr 1
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro q
    dsimp only
    rw [norm_sq_shapeCoordinateEquiv,←sum_shapeExtend_sq]
    change _=firstVandermonde (shapeExtend q)^2*(w (c*(∑ i,shapeExtend q i^2)/tau)/
      (tau+c*(∑ i,shapeExtend q i^2))^(j+1))
    unfold constrainedBetaKernel
    ring
  · have hi : (∫ r in Ioi (0:ℝ),r^(n-1+(n+1)*n)*w (c*r^2/tau)/(tau+c*r^2)^(j+1))=
        ∫ r in Ioi (0:ℝ),r^(n-1+(n+1)*n)*(w (c*r^2/tau)/(tau+c*r^2)^(j+1)) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro r
      ring
    rw [hi]
    simp only [shapeAngularConstant,Complex.real_smul,Complex.ofReal_mul,mul_assoc]

/-- Exact beta probability normalization for arbitrary radial weights in the
actual independent coordinates, including the 1/sqrt(n+1) Jacobian. -/
theorem weightedShapeBeta_normalized {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : alpha (n+1)≤j) (tau c : ℝ) (ht : 0<tau) (hc : 0<c)
    (w : ℝ → ℝ) :
    (∫ q : Fin n → ℝ,w (c*(∑ i : Fin (n+1),shapeExtend q i^2)/tau)*
      constrainedBetaKernel n j tau c q)/constrainedBetaValue (n+1) j tau c=
      (∫ x in Ioi (0:ℝ),w x*(x^(alpha (n+1)-1)/(1+x)^(j+1)))/betaMass (alpha (n+1)) j := by
  have ha : 0<alpha (n+1) := by
    rw [alpha_eq_derivativeOrder]
    exact IsingBulk.HT.First.derivativeOrder_pos ho (by omega)
  have hdegree : n-1+(n+1)*n=2*alpha (n+1)-1 := by
    rw [alpha_eq_derivativeOrder]
    simpa only [Nat.add_sub_cancel] using IsingBulk.HT.First.odd_shape_radial_exponent ho (by omega)
  have hw := weightedShapeBeta_radial (show 1≤n by omega) j tau c w
  rw [hdegree,weightedRadialBeta_order _ j ha tau c ht hc w] at hw
  have h1 := weightedShapeBeta_radial (show 1≤n by omega) j tau c (fun _=>1)
  rw [hdegree,weightedRadialBeta_order _ j ha tau c ht hc (fun _=>1)] at h1
  simp only [one_mul,mul_one] at h1
  rw [constrainedBetaKernel_integral ho hn j hj tau c ht hc] at h1
  change constrainedBetaValue (n+1) j tau c=
    shapeAngularConstant n*((tau/c)^alpha (n+1)/(2*tau^(j+1))*betaMass (alpha (n+1)) j) at h1
  have hconst : shapeAngularConstant n*((tau/c)^alpha (n+1)/(2*tau^(j+1)))≠0 := by
    have hshape := shapeAngularConstant_pos (show 1≤n by omega)
    positivity
  rw [hw,h1]
  simp_rw [show ∀x : ℝ,x^(alpha (n+1)-1)*w x/(1+x)^(j+1)=
    w x*(x^(alpha (n+1)-1)/(1+x)^(j+1)) by intro x; ring]
  rw [←mul_assoc,←mul_assoc]
  exact mul_div_mul_left _ _ hconst

end
end IsingBulk.Anisotropic.NegativeNormalForm
