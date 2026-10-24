import IsingBulk.Anisotropic.NegativeCycles.FreeHomotopy

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm

def complexSpatial (n : ℕ) : ParameterSpace n→L[ℝ] Config n :=
  (complexify n).comp (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i.succ))

def complexTime (n : ℕ) : ParameterSpace n→L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj 0)

@[simp] theorem complexSpatial_apply (n : ℕ) (x : ParameterSpace n) (i : Fin n) :
    complexSpatial n x i=(x i.succ:ℂ) := rfl
@[simp] theorem complexTime_apply (n : ℕ) (x : ParameterSpace n) :
    complexTime n x=(x 0:ℂ) := rfl

theorem freeStraightHomotopy_fderiv {n : ℕ} (Psi : Config n→Config n)
    (x u : ParameterSpace n) (hPsi : DifferentiableAt ℂ Psi (complexSpatial n x)) :
    fderiv ℝ (freeStraightHomotopy Psi) x u=
      complexSpatial n u+(complexTime n u) • (Psi (complexSpatial n x)-complexSpatial n x)+
        (complexTime n x) • (fderiv ℂ Psi (complexSpatial n x) (complexSpatial n u)-complexSpatial n u) := by
  have hc := (complexSpatial n).hasFDerivAt (x := x)
  have ht := (complexTime n).hasFDerivAt (x := x)
  have hp := (hPsi.hasFDerivAt.restrictScalars ℝ).comp x hc
  have hh := hc.add (ht.smul (hp.sub hc))
  change HasFDerivAt (freeStraightHomotopy Psi) _ x at hh
  rw [hh.fderiv]
  change complexSpatial n u+((complexTime n x) •
    (fderiv ℂ Psi (complexSpatial n x) (complexSpatial n u)-complexSpatial n u)+
    (complexTime n u) • (Psi (complexSpatial n x)-complexSpatial n x))=_
  abel

@[simp] theorem complexSpatial_single_succ (n : ℕ) (i : Fin n) :
    complexSpatial n (Pi.single i.succ (1:ℝ))=Pi.single i (1:ℂ) := by
  ext j
  by_cases h : j=i
  · subst j
    simp
  · simp [h,Fin.succ_inj]

@[simp] theorem complexTime_single_succ (n : ℕ) (i : Fin n) :
    complexTime n (Pi.single i.succ (1:ℝ))=0 := by simp

@[simp] theorem complexSpatial_single_zero (n : ℕ) :
    complexSpatial n (Pi.single (0:Fin (n+1)) (1:ℝ))=0 := by ext i; simp

@[simp] theorem complexTime_single_zero (n : ℕ) :
    complexTime n (Pi.single (0:Fin (n+1)) (1:ℝ))=1 := by simp

theorem freeStraightHomotopy_spatial_derivative {n : ℕ} (Psi : Config n→Config n)
    (x : ParameterSpace n) (hPsi : DifferentiableAt ℂ Psi (complexSpatial n x)) (i : Fin n) :
    fderiv ℝ (freeStraightHomotopy Psi) x (Pi.single i.succ (1:ℝ))=
      Pi.single i (1:ℂ)+(x 0:ℂ) • (fderiv ℂ Psi (complexSpatial n x) (Pi.single i (1:ℂ))-Pi.single i (1:ℂ)) := by
  rw [freeStraightHomotopy_fderiv Psi x _ hPsi]
  simp

theorem freeStraightHomotopy_time_derivative {n : ℕ} (Psi : Config n→Config n)
    (x : ParameterSpace n) (hPsi : DifferentiableAt ℂ Psi (complexSpatial n x)) :
    fderiv ℝ (freeStraightHomotopy Psi) x (Pi.single (0:Fin (n+1)) (1:ℝ))=
      Psi (complexSpatial n x)-complexSpatial n x := by
  rw [freeStraightHomotopy_fderiv Psi x _ hPsi]
  simp

end IsingBulk.Anisotropic.NegativeCycles
