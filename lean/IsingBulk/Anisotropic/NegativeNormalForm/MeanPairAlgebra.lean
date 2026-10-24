import IsingBulk.Anisotropic.NegativeNormalForm.RootPairBounds
import IsingBulk.Anisotropic.NegativeNormalForm.MeanCoefficients

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

theorem meanCoefficients_difference {n : ℕ} (S : Config n) (i j : Fin n)
    (hi : S i≠0) (hj : S j≠0) (_hden : (∑ k, (S k)⁻¹)≠0) :
    meanCoefficients S i-meanCoefficients S j=(S i-S j)/(S i*S j*(∑ k, (S k)⁻¹)) := by
  unfold meanCoefficients project
  dsimp
  field_simp
  ring

/-- Exact full mean-corrected pair denominator. All denominators are scalar
roots or their reciprocal sum; the complex quadratic cone is never divided by. -/
def correctedSeparablePairFactor {n : ℕ} (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (t d : ℂ) (v : Config n) (i j : Fin n) : ℂ :=
  let S : Config n := fun k => rootScalar B phi hphi (t,(d,v k))
  separablePairFactor B phi hphi t d (v i) (v j)+
    rankOneCoefficient (meanCoefficients S)*mean (fun k => v k*S k)*
      (rootPairSlope B phi hphi t d (v i) (v j)/(S i*S j*(∑ k, (S k)⁻¹)))

 theorem correctedSeparablePairFactor_identity {n : ℕ} (hn : n≠0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (t d : ℂ) (v : Config n)
    (hv : ZeroMean v) (i j : Fin n)
    (hS : ∀ k, rootScalar B phi hphi (t,(d,v k))≠0)
    (hden : (∑ k, (rootScalar B phi hphi (t,(d,v k)))⁻¹)≠0)
    (hroot : rootScalar B phi hphi (t,(d,v i))-rootScalar B phi hphi (t,(d,v j))=
      (v i-v j)*rootPairSlope B phi hphi t d (v i) (v j))
    (hsep : v i*rootScalar B phi hphi (t,(d,v i))-v j*rootScalar B phi hphi (t,(d,v j))=
      (v i-v j)*separablePairFactor B phi hphi t d (v i) (v j)) :
    let S : Config n := fun k => rootScalar B phi hphi (t,(d,v k))
    let w := project (fun k => v k*S k)
    meanCorrection (meanCoefficients S) w i-meanCorrection (meanCoefficients S) w j=
      (v i-v j)*correctedSeparablePairFactor B phi hphi t d v i j := by
  dsimp only
  let S : Config n := fun k => rootScalar B phi hphi (t,(d,v k))
  let w := project (fun k => v k*S k)
  have hm := meanCoefficients_factorization v w S hv (project_zeroMean hn _) hS hden rfl
  have hp : w i-w j=v i*S i-v j*S j := by dsimp [w,project]; ring
  change meanCorrection (meanCoefficients S) w i-meanCorrection (meanCoefficients S) w j=_
  rw [meanCorrection_difference,hm,hp,meanCoefficients_difference S i j (hS i) (hS j) hden]
  change v i*rootScalar B phi hphi (t,(d,v i))-v j*rootScalar B phi hphi (t,(d,v j))+
    rankOneCoefficient (meanCoefficients S)*mean (fun k => v k*S k)*
      ((rootScalar B phi hphi (t,(d,v i))-rootScalar B phi hphi (t,(d,v j)))/(S i*S j*(∑ k,(S k)⁻¹)))=_
  rw [hroot,hsep]
  unfold correctedSeparablePairFactor
  simp only [div_eq_mul_inv]
  ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
