import IsingBulk.Anisotropic.NegativeNormalForm.Algebra
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-! The actual complex Jacobian in the n-1 free coordinates of the zero-mean hyperplane. -/
noncomputable section
open scoped BigOperators
namespace IsingBulk.Anisotropic.NegativeNormalForm

def freeChartCLM (m : ℕ) : Config m →L[ℂ] Config (m+1) :=
  ContinuousLinearMap.pi (Fin.lastCases (-∑ i, ContinuousLinearMap.proj i)
    (fun i => ContinuousLinearMap.proj i))

def freeCoordinatesCLM (m : ℕ) : Config (m+1) →L[ℂ] Config m :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.castSucc

@[simp] theorem freeChartCLM_castSucc (m : ℕ) (u : Config m) (i : Fin m) :
    freeChartCLM m u i.castSucc = u i := by simp [freeChartCLM]

@[simp] theorem freeChartCLM_last (m : ℕ) (u : Config m) :
    freeChartCLM m u (Fin.last m) = -∑ i, u i := by simp [freeChartCLM]

@[simp] theorem freeCoordinatesCLM_apply (m : ℕ) (v : Config (m+1)) (i : Fin m) :
    freeCoordinatesCLM m v i = v i.castSucc := rfl

 theorem freeChartCLM_zeroMean (m : ℕ) (u : Config m) : ZeroMean (freeChartCLM m u) := by
  unfold ZeroMean
  rw [Fin.sum_univ_castSucc]
  simp

@[simp] theorem freeCoordinates_freeChart (m : ℕ) :
    (freeCoordinatesCLM m).comp (freeChartCLM m) = ContinuousLinearMap.id ℂ (Config m) := by
  ext u i
  simp

def constrainedMap {m : ℕ} (Phi : Config (m+1) → Config (m+1)) (u : Config m) : Config m :=
  freeCoordinatesCLM m (Phi (freeChartCLM m u))

def constrainedJacobian {m : ℕ} (Phi : Config (m+1) → Config (m+1)) (u : Config m) : ℂ :=
  Matrix.det (fun i j => fderiv ℂ (constrainedMap Phi) u (Pi.single j 1) i)

 theorem constrainedMap_analyticAt {m : ℕ} (Phi : Config (m+1) → Config (m+1))
    (hPhi : AnalyticAt ℂ Phi 0) : AnalyticAt ℂ (constrainedMap Phi) 0 := by
  exact ((freeCoordinatesCLM m).analyticAt _).comp
    (hPhi.comp_of_eq ((freeChartCLM m).analyticAt 0) (map_zero _))

 theorem constrainedMap_hasFDerivAt {m : ℕ} (Phi : Config (m+1) → Config (m+1))
    (hd : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config (m+1))) 0) :
    HasFDerivAt (constrainedMap Phi) (ContinuousLinearMap.id ℂ (Config m)) 0 := by
  have hd' : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config (m+1))) (freeChartCLM m 0) := by
    simpa using hd
  have h1 := hd'.comp (f := fun u => freeChartCLM m u) 0 ((freeChartCLM m).hasFDerivAt (x := 0))
  have h := ((freeCoordinatesCLM m).hasFDerivAt (x := Phi (freeChartCLM m 0))).comp 0 h1
  simp only [ContinuousLinearMap.id_comp,freeCoordinates_freeChart] at h
  convert! h using 1

 theorem constrainedJacobian_analyticAt {m : ℕ} (Phi : Config (m+1) → Config (m+1))
    (hPhi : AnalyticAt ℂ Phi 0) : AnalyticAt ℂ (constrainedJacobian Phi) 0 := by
  have hD := (constrainedMap_analyticAt Phi hPhi).fderiv
  have hentry (i j : Fin m) : AnalyticAt ℂ
      (fun u => fderiv ℂ (constrainedMap Phi) u (Pi.single j 1) i) 0 := by
    let L : (Config m →L[ℂ] Config m) →L[ℂ] Config m :=
      ContinuousLinearMap.apply ℂ (Config m) (Pi.single j 1)
    exact (analyticAt_pi_iff.mp ((L.analyticAt _).comp hD)) i
  have he : constrainedJacobian Phi = fun u =>
      ∑ e : Equiv.Perm (Fin m), (Equiv.Perm.sign e : ℂ) *
        ∏ i, fderiv ℂ (constrainedMap Phi) u (Pi.single i 1) (e i) := by
    funext u
    exact Matrix.det_apply' _
  rw [he]
  apply Finset.analyticAt_fun_sum
  intro e _
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod
  intro i _
  exact hentry _ _

@[simp] theorem constrainedJacobian_zero {m : ℕ} (Phi : Config (m+1) → Config (m+1))
    (hd : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config (m+1))) 0) :
    constrainedJacobian Phi 0 = 1 := by
  unfold constrainedJacobian
  rw [(constrainedMap_hasFDerivAt Phi hd).fderiv]
  have hmat : (fun i j : Fin m => (ContinuousLinearMap.id ℂ (Config m)) (Pi.single j 1) i) =
      (1 : Matrix (Fin m) (Fin m) ℂ) := by
    ext i j
    simp [Matrix.one_apply,Pi.single_apply]
  rw [hmat,Matrix.det_one]

end IsingBulk.Anisotropic.NegativeNormalForm
