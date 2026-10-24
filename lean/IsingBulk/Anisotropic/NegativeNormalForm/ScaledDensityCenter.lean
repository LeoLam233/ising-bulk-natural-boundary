import IsingBulk.Anisotropic.NegativeNormalForm.CanonicalNormalForm
import IsingBulk.Anisotropic.NegativeNormalForm.FullTransformedDensity

/-! Exact central scaling of every factor of the full constrained density. -/
noncomputable section
open IsingBulk.First
open scoped BigOperators
namespace IsingBulk.Anisotropic.NegativeNormalForm

 theorem coincidenceFactor_zero_scalar {n : ℕ} (Phi : Config n → Config n) (c : ℂ)
    (hd : HasFDerivAt Phi (scalarConfiguration c) 0)
    (i j : Fin n) (hij : i ≠ j) : coincidenceFactor Phi i j 0 = c := by
  let L : Config n →L[ℂ] ℂ := (ContinuousLinearMap.proj i : Config n →L[ℂ] ℂ) -
    (ContinuousLinearMap.proj j : Config n →L[ℂ] ℂ)
  have hd' : HasFDerivAt Phi (scalarConfiguration c) (collisionInsert i j 0) := by
    simpa using hd
  have hcomp := hd'.comp (f := fun z => collisionInsert i j z) 0
    ((collisionInsert i j).hasFDerivAt (x := 0))
  have hfun : HasFDerivAt (collisionFunction Phi i j)
      (L.comp ((scalarConfiguration c).comp (collisionInsert i j))) 0 := by
    convert! (L.hasFDerivAt (x := Phi (collisionInsert i j 0))).comp
      (f := fun z => Phi (collisionInsert i j z)) 0 hcomp using 1
  change coordinateHadamard (collisionFunction Phi i j) (0,0-0) = c
  rw [sub_self,show ((0 : Config n),(0 : ℂ)) = 0 from rfl,coordinateHadamard_zero,hfun.fderiv]
  simp [L,scalarConfiguration,Ne.symm hij]


 theorem constrainedMap_hasFDerivAt_scalar {m : ℕ} (Phi : Config (m+1) → Config (m+1)) (c : ℂ)
    (hd : HasFDerivAt Phi (scalarConfiguration c) 0) :
    HasFDerivAt (constrainedMap Phi) (scalarConfiguration c) 0 := by
  have hd' : HasFDerivAt Phi (scalarConfiguration c) (freeChartCLM m 0) := by simpa using hd
  have h1 := hd'.comp (f := fun u => freeChartCLM m u) 0 ((freeChartCLM m).hasFDerivAt (x := 0))
  have h := ((freeCoordinatesCLM m).hasFDerivAt (x := Phi (freeChartCLM m 0))).comp 0 h1
  simp only [scalarConfiguration,ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.id_comp,freeCoordinates_freeChart] at h
  convert! h using 1

 theorem constrainedJacobian_zero_scalar {m : ℕ} (Phi : Config (m+1) → Config (m+1)) (c : ℂ)
    (hd : HasFDerivAt Phi (scalarConfiguration c) 0) : constrainedJacobian Phi 0 = c^m := by
  unfold constrainedJacobian
  rw [(constrainedMap_hasFDerivAt_scalar Phi c hd).fderiv]
  have hmat : (fun i j : Fin m => scalarConfiguration c (Pi.single j 1) i) =
      c • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    ext i j
    simp [Matrix.one_apply,Pi.single_apply]
  rw [hmat,Matrix.det_smul,Matrix.det_one]
  simp

 theorem actualPairMultiplier_zero_scalar {n : ℕ} (Phi : Config n → Config n) (c : ℂ)
    (hd : HasFDerivAt Phi (scalarConfiguration c) 0) : actualPairMultiplier Phi 0 = c^(n.choose 2) := by
  calc
    _ = ∏ p ∈ firstStrictPairs n, c := by
      apply Finset.prod_congr rfl
      intro p hp
      exact coincidenceFactor_zero_scalar Phi c hd p.1 p.2
        (ne_of_lt (mem_firstStrictPairs p |>.mp hp))
    _ = _ := by simp [firstStrictPairs_card]

 theorem fullTransformedDensity_zero_scalar {m : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (T : Config (m+1) → ℂ)
    (Phi : Config (m+1) → Config (m+1)) (hPhi0 : Phi 0=0) (c : ℂ)
    (hd : HasFDerivAt Phi (scalarConfiguration c) 0) :
    fullTransformedDensity B rootB phi hphi d T Phi 0 =
      regularResidue B rootB phi hphi d T 0 * c^(m*(m+2)) := by
  simp only [fullTransformedDensity,map_zero,hPhi0,actualPairMultiplier_zero_scalar Phi c hd,
    constrainedJacobian_zero_scalar Phi c hd]
  have hcard := firstStrictPairs_twice_card m
  rw [firstStrictPairs_card] at hcard
  have hexp : (m+1).choose 2*2+m=m*(m+2) := by nlinarith [hcard]
  rw [← pow_mul,mul_assoc,← pow_add,hexp]

 theorem fullTransformedDensity_zero_hessian {m : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (d : ℂ) (T : Config (m+1) → ℂ)
    (Psi : Config (m+1) → Config (m+1)) (hPsi0 : Psi 0=0)
    (hd : HasFDerivAt Psi (scalarConfiguration (Complex.sqrt (centralHessian B phi d))⁻¹) 0)
    (a : ℕ) (ha : m*(m+2)=2*a) :
    fullTransformedDensity B rootB phi hphi d T Psi 0 =
      regularResidue B rootB phi hphi d T 0 * ((centralHessian B phi d)^a)⁻¹ := by
  rw [fullTransformedDensity_zero_scalar B rootB phi hphi d T Psi hPsi0 _ hd,ha,
    pow_mul,inv_pow,sqrt_sq,inv_pow]

end IsingBulk.Anisotropic.NegativeNormalForm
