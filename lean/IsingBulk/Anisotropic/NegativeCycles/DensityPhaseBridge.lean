import IsingBulk.Anisotropic.NegativeCycles.HyperbolicDensity
import IsingBulk.Anisotropic.NegativeCycles.ComplexNumeratorFactor
import IsingBulk.Anisotropic.NegativeDominance.ContinuationDensity

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.RegularEdges
open scoped BigOperators

theorem firstStrictPairs_prod_indexed (N : ℕ) (f : Fin N→Fin N→ℂ) :
    (∏p∈firstStrictPairs N,f p.1 p.2)=(∏i,∏j∈Finset.univ.filter (fun j => i<j),f i j) := by
  simp [firstStrictPairs,Finset.prod_filter,Fintype.prod_prod_type]

theorem odd_density_scalar (m : ℕ) (A S B R : ℂ) (hAR : A/S=R) (hR : R^2=B) :
    A^(2*m+1)*B^((2*m+1).choose 2)*S⁻¹^(2*m+1)=R*B^(alpha (2*m+1)) := by
  have hAS : A^(2*m+1)*S⁻¹^(2*m+1)=R^(2*m+1) := by
    rw [←mul_pow,←div_eq_mul_inv,hAR]
  have hpow : R^(2*m+1)=R*B^m := by rw [pow_add,pow_mul,hR,pow_one]; ring
  rw [alpha_eq_pairs_add,pow_add]
  calc
    _ = (A^(2*m+1)*S⁻¹^(2*m+1))*B^((2*m+1).choose 2) := by ring
    _ = _ := by rw [hAS,hpow]; ring

/-- Literal continued angular weight, with every scalar and factorial retained. -/
theorem scaled_continuedAngularWeight_eq_formFactorNumerator (m : ℕ)
    (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d t : ℂ)
    (v : Config (2*m+1)) {lam : ℝ} {z A : ℂ}
    (hB : B t=spectralT lam z/spectralS z) (hAR : A/spectralS z=rootB t)
    (hR : (rootB t)^2=B t)
    (hroot : ∀i, continuedTransferRoot lam z ((Real.pi:ℂ)+d+v i)=
      Complex.exp (-negativePhase B phi hphi t (d+v i))) :
    A^(2*m+1)/(((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))*
      continuedAngularWeight lam z (fun i => (Real.pi:ℂ)+d+v i)=
        formFactorNumerator B rootB phi hphi d t v := by
  unfold continuedAngularWeight
  simp_rw [hroot,rootOneBody_exp_neg,angularRootPair_exp_neg]
  have hp : (∏i,∏j∈Finset.univ.filter (fun j => i<j),
      (Complex.sin ((((Real.pi:ℂ)+d+v i)-((Real.pi:ℂ)+d+v j))/2)/
       Complex.sinh ((negativePhase B phi hphi t (d+v i)+negativePhase B phi hphi t (d+v j))/2))^2)=
      ∏p∈firstStrictPairs (2*m+1),
        (Complex.sin ((v p.1-v p.2)/2)/pairDenominator B phi hphi d t (v p.1) (v p.2))^2 := by
    rw [firstStrictPairs_prod_indexed (2*m+1) (fun i j =>
      (Complex.sin ((v i-v j)/2)/pairDenominator B phi hphi d t (v i) (v j))^2)]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    unfold pairDenominator
    congr 3
    ring
  rw [hp,←hB]
  unfold formFactorNumerator densityPrefactor
  have hs := odd_density_scalar m A (spectralS z) (B t) (rootB t) hAR hR
  have hn : 2*m+1-1=2*m := by omega
  rw [hn]
  calc
    _ = (A^(2*m+1)*(B t)^((2*m+1).choose 2)*(spectralS z)⁻¹^(2*m+1))/
        (((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))*
        (∏i,(Complex.sinh (negativePhase B phi hphi t (d+v i)))⁻¹)*
        (∏p∈firstStrictPairs (2*m+1),
          (Complex.sin ((v p.1-v p.2)/2)/pairDenominator B phi hphi d t (v p.1) (v p.2))^2) := by ring
    _ = _ := by rw [hs]

/-- At resonance the exact physical density has the proved coth kernel. -/
theorem scaled_continuedAngularDensity_eq_phase (m : ℕ)
    (B rootB : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d t : ℂ)
    (v : Config (2*m+1)) {lam : ℝ} {z A : ℂ}
    (hB : B t=spectralT lam z/spectralS z) (hAR : A/spectralS z=rootB t)
    (hR : (rootB t)^2=B t)
    (hroot : ∀i, continuedTransferRoot lam z ((Real.pi:ℂ)+d+v i)=
      Complex.exp (-negativePhase B phi hphi t (d+v i)))
    (hres : Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1) :
    A^(2*m+1)/(((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))*
      continuedAngularDensity lam z (fun i => (Real.pi:ℂ)+d+v i)=
        formFactorNumerator B rootB phi hphi d t v *
          cothHalf (fun u => poleEquation B phi hphi d u v) t := by
  unfold continuedAngularDensity
  rw [←mul_assoc,scaled_continuedAngularWeight_eq_formFactorNumerator m B rootB phi hphi d t v hB hAR hR hroot]
  simp_rw [hroot]
  rw [rootKernel_exp_neg]
  exact congrArg (fun w => formFactorNumerator B rootB phi hphi d t v*w)
    (resonant_kernel_eq B phi hphi d t v hres)

end IsingBulk.Anisotropic.NegativeCycles
