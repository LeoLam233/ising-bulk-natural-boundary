import IsingBulk.Anisotropic.NegativeCycles.FreeHomotopyDerivative

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm Set MeasureTheory

def complexJacobian {n : ℕ} (Psi : Config n→Config n) (q : Config n) : ℂ :=
  Matrix.det (fun i j => fderiv ℂ Psi q (Pi.single j 1) i)

theorem explicit_cap_zero {n : ℕ} (bump : ContDiffBump (0:ℝ))
    (f : Config n→ℂ) (Psi : Config n→Config n) (q : Fin n→ℝ)
    (hPsi : DifferentiableAt ℂ Psi (complexify n q)) :
    (shapeCylinderCutoff bump (Fin.cons 0 q) •
      chainPullback (densityForm f) (freeStraightHomotopy Psi) (Fin.cons 0 q))
        (fun i => Pi.single i.succ (1:ℝ))=
      (shapeSpatialCutoff bump q:ℂ)*f (complexify n q) := by
  have hc : complexSpatial n (Fin.cons 0 q)=complexify n q := by ext i; simp
  have hd (i : Fin n) : fderiv ℝ (freeStraightHomotopy Psi) (Fin.cons 0 q)
      (Pi.single i.succ (1:ℝ))=Pi.single i (1:ℂ) := by
    simpa using freeStraightHomotopy_spatial_derivative Psi (Fin.cons 0 q) (by simpa only [hc] using hPsi) i
  have hdet : Matrix.det (fun i : Fin n => Pi.single i (1:ℂ))=1 := by
    convert Matrix.det_one (n := Fin n) (R := ℂ) using 1
    congr 1
    ext i j
    simp [Matrix.one_apply,Pi.single_apply,eq_comm]
  have hcut : shapeCylinderCutoff bump (Fin.cons 0 q)=shapeSpatialCutoff bump q := by
    simpa using shapeCylinderCutoff_on_interval bump (x := Fin.cons 0 q) (by simp)
  simp only [ContinuousAlternatingMap.smul_apply,densityForm_chainPullback,hd,hdet,mul_one,hcut]
  simp [freeStraightHomotopy,Complex.real_smul]

theorem explicit_cap_one {n : ℕ} (bump : ContDiffBump (0:ℝ))
    (f : Config n→ℂ) (Psi : Config n→Config n) (q : Fin n→ℝ)
    (hPsi : DifferentiableAt ℂ Psi (complexify n q)) :
    (shapeCylinderCutoff bump (Fin.cons 1 q) •
      chainPullback (densityForm f) (freeStraightHomotopy Psi) (Fin.cons 1 q))
        (fun i => Pi.single i.succ (1:ℝ))=
      (shapeSpatialCutoff bump q:ℂ)*f (Psi (complexify n q))*complexJacobian Psi (complexify n q) := by
  have hc : complexSpatial n (Fin.cons 1 q)=complexify n q := by ext i; simp
  have hd (i : Fin n) : fderiv ℝ (freeStraightHomotopy Psi) (Fin.cons 1 q)
      (Pi.single i.succ (1:ℝ))=fderiv ℂ Psi (complexify n q) (Pi.single i (1:ℂ)) := by
    have hh := freeStraightHomotopy_spatial_derivative Psi (Fin.cons 1 q) (by simpa only [hc] using hPsi) i
    simp only [hc,Fin.cons_zero,Complex.ofReal_one,one_smul] at hh
    convert hh using 1
    abel
  have hdet : Matrix.det (fun i : Fin n => fderiv ℂ Psi (complexify n q) (Pi.single i (1:ℂ)))=
      complexJacobian Psi (complexify n q) := by
    exact Matrix.det_transpose _
  have hcut : shapeCylinderCutoff bump (Fin.cons 1 q)=shapeSpatialCutoff bump q := by
    simpa using shapeCylinderCutoff_on_interval bump (x := Fin.cons 1 q) (by simp)
  simp only [ContinuousAlternatingMap.smul_apply,densityForm_chainPullback,hd,hdet,hcut]
  simp [freeStraightHomotopy,Complex.real_smul,mul_assoc]

theorem boxCapIntegral_zero_eq {n : ℕ} (bump : ContDiffBump (0:ℝ))
    (f : Config n→ℂ) (Psi : Config n→Config n) (a b : ParameterSpace n)
    (hPsi : ∀q : Fin n→ℝ, constrainedSquaredRadius q≤bump.rOut →
      DifferentiableAt ℂ Psi (complexify n q)) :
    boxCapIntegral (fun x => shapeCylinderCutoff bump x •
      chainPullback (densityForm f) (freeStraightHomotopy Psi) x) a b 0=
      ∫q in Icc (fun i => a i.succ) (fun i => b i.succ),
        (shapeSpatialCutoff bump q:ℂ)*f (complexify n q) := by
  simp only [boxCapIntegral,Fin.succAbove_zero,Fin.insertNth_zero',Fin.removeNth_zero]
  apply setIntegral_congr_fun measurableSet_Icc
  intro q _
  by_cases hq : constrainedSquaredRadius q≤bump.rOut
  · exact explicit_cap_zero bump f Psi q (hPsi q hq)
  · have hz := shapeSpatialCutoff_zero bump (le_of_not_ge hq)
    have hcz : shapeCylinderCutoff bump (Fin.cons 0 q)=0 := by simp [shapeCylinderCutoff,hz]
    simp [hcz,hz]

theorem boxCapIntegral_one_eq {n : ℕ} (bump : ContDiffBump (0:ℝ))
    (f : Config n→ℂ) (Psi : Config n→Config n) (a b : ParameterSpace n)
    (hPsi : ∀q : Fin n→ℝ, constrainedSquaredRadius q≤bump.rOut →
      DifferentiableAt ℂ Psi (complexify n q)) :
    boxCapIntegral (fun x => shapeCylinderCutoff bump x •
      chainPullback (densityForm f) (freeStraightHomotopy Psi) x) a b 1=
      ∫q in Icc (fun i => a i.succ) (fun i => b i.succ),
        (shapeSpatialCutoff bump q:ℂ)*f (Psi (complexify n q))*complexJacobian Psi (complexify n q) := by
  simp only [boxCapIntegral,Fin.succAbove_zero,Fin.insertNth_zero',Fin.removeNth_zero]
  apply setIntegral_congr_fun measurableSet_Icc
  intro q _
  by_cases hq : constrainedSquaredRadius q≤bump.rOut
  · exact explicit_cap_one bump f Psi q (hPsi q hq)
  · have hz := shapeSpatialCutoff_zero bump (le_of_not_ge hq)
    have hcz : shapeCylinderCutoff bump (Fin.cons 1 q)=0 := by simp [shapeCylinderCutoff,hz]
    simp [hcz,hz]

end IsingBulk.Anisotropic.NegativeCycles
