import IsingBulk.Anisotropic.NegativeNormalForm.DensityJacobianSpectrum
import IsingBulk.Anisotropic.NegativeNormalForm.ConstrainedJacobian

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem freeChart_freeCoordinates {m : ℕ} {v : Config (m+1)} (hv : ZeroMean v) :
    freeChartCLM m (freeCoordinatesCLM m v)=v := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hh : (∑j : Fin m,v j.castSucc)+v (Fin.last m)=0 := by
      simpa only [ZeroMean,Fin.sum_univ_castSucc] using hv
    simp only [freeChartCLM_last,freeCoordinatesCLM_apply]
    linear_combination -hh
  · simp

theorem freeChart_injective (m : ℕ) : Function.Injective (freeChartCLM m) := by
  intro x y h
  have hh := congrArg (freeCoordinatesCLM m) h
  simpa only [←ContinuousLinearMap.comp_apply,freeCoordinates_freeChart,ContinuousLinearMap.id_apply] using hh

def constrainedDerivative {m : ℕ} (L : Config (m+1)→L[ℂ]Config (m+1)) : Config m→L[ℂ]Config m :=
  (freeCoordinatesCLM m).comp (L.comp (freeChartCLM m))

theorem constrainedDerivative_intertwines {m : ℕ} (L : Config (m+1)→L[ℂ]Config (m+1))
    (hL : ∀v,ZeroMean (L (freeChartCLM m v))) (v : Config m) :
    L (freeChartCLM m v)=freeChartCLM m (constrainedDerivative L v) :=
  (freeChart_freeCoordinates (hL v)).symm

theorem constrainedMap_fderiv {m : ℕ} {Phi : Config (m+1)→Config (m+1)} {u : Config m}
    (hd : DifferentiableAt ℂ Phi (freeChartCLM m u)) :
    fderiv ℂ (constrainedMap Phi) u=constrainedDerivative (fderiv ℂ Phi (freeChartCLM m u)) := by
  have hh := ((freeCoordinatesCLM m).hasFDerivAt (x := Phi (freeChartCLM m u))).comp u
    (hd.hasFDerivAt.comp u ((freeChartCLM m).hasFDerivAt (x := u)))
  exact hh.fderiv

theorem constrainedJacobian_eq_det {m : ℕ} {Phi : Config (m+1)→Config (m+1)} {u : Config m}
    (hd : DifferentiableAt ℂ Phi (freeChartCLM m u)) :
    constrainedJacobian Phi u=(constrainedDerivative (fderiv ℂ Phi (freeChartCLM m u))).toLinearMap.det := by
  unfold constrainedJacobian
  rw [constrainedMap_fderiv hd,←LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin m))]
  congr 1

theorem fderiv_freeChart_zeroMean {m : ℕ} {Phi : Config (m+1)→Config (m+1)}
    {U : Set (Config (m+1))} (hU : IsOpen U) {u : Config m} (hu : freeChartCLM m u∈U)
    (hd : DifferentiableAt ℂ Phi (freeChartCLM m u))
    (hmean : ∀v∈U,ZeroMean v → ZeroMean (Phi v)) (v : Config m) :
    ZeroMean (fderiv ℂ Phi (freeChartCLM m u) (freeChartCLM m v)) := by
  have hD := ((meanCLM (m+1)).hasFDerivAt (x := Phi (freeChartCLM m u))).comp u
    (hd.hasFDerivAt.comp u ((freeChartCLM m).hasFDerivAt (x := u)))
  have he : (fun w => meanCLM (m+1) (Phi (freeChartCLM m w)))=ᶠ[𝓝 u] (fun _ => (0:ℂ)) := by
    filter_upwards [(freeChartCLM m).continuous.continuousAt.eventually (hU.mem_nhds hu)] with w hw
    simpa only [meanCLM_apply] using (mean_eq_zero_iff (Nat.succ_ne_zero m) _).mpr (hmean _ hw (freeChartCLM_zeroMean m w))
  have hzero : HasFDerivAt (fun w => meanCLM (m+1) (Phi (freeChartCLM m w))) 0 u :=
    (hasFDerivAt_const (𝕜 := ℂ) (0:ℂ) u).congr_of_eventuallyEq he
  have hh := congrArg (fun L : Config m→L[ℂ]ℂ => L v) (hD.unique hzero)
  apply (mean_eq_zero_iff (Nat.succ_ne_zero m) _).mp
  simpa only [ContinuousLinearMap.comp_apply,zero_apply,meanCLM_apply] using hh

theorem constrainedJacobian_norm_bounds {m : ℕ} {Phi : Config (m+1)→Config (m+1)}
    {U : Set (Config (m+1))} (hU : IsOpen U) {u : Config m} (hu : freeChartCLM m u∈U)
    (hd : DifferentiableAt ℂ Phi (freeChartCLM m u))
    (hmean : ∀v∈U,ZeroMean v → ZeroMean (Phi v)) {eps : ℝ} (heps : eps≤1)
    (hL : ‖fderiv ℂ Phi (freeChartCLM m u)-ContinuousLinearMap.id ℂ (Config (m+1))‖≤eps) :
    (1-eps)^m≤‖constrainedJacobian Phi u‖ ∧ ‖constrainedJacobian Phi u‖≤(1+eps)^m := by
  rw [constrainedJacobian_eq_det hd]
  simpa using lifted_det_norm_bounds _ _ (freeChartCLM m) (freeChart_injective m)
    (constrainedDerivative_intertwines _ (fderiv_freeChart_zeroMean hU hu hd hmean)) heps hL


/-- Actual corrected normal-form Jacobian bounds on the full common ball. -/
theorem UniformCorrectionWitness.constrainedJacobian_bounds {m : ℕ}
    (B : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C R : ℝ)
    (P : UniformProjectedWitness B phi hphi (m+1) d r C)
    (J : UniformCorrectionWitness B phi hphi (m+1) d r C P R)
    (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) (u : Config m)
    (hu : ‖freeChartCLM m u‖<R/2) :
    (29/32:ℝ)^m≤‖constrainedJacobian (fun y => P.V (J.W y)) u‖ ∧
      ‖constrainedJacobian (fun y => P.V (J.W y)) u‖≤(35/32:ℝ)^m := by
  have hUa := (J.corrected_bounds B phi hphi d r C R P hr hR hRr).1
  have huU : freeChartCLM m u∈Metric.ball 0 (R/2) := by simpa using hu
  have hmean : ∀y∈Metric.ball (0:Config (m+1)) (R/2),ZeroMean y → ZeroMean (P.V (J.W y)) := by
    intro y hy hm
    have hy' : ‖y‖≤R/2 := le_of_lt (by simpa using hy)
    have hw := J.w_inverse y hy'
    exact ((P.v_inverse (J.W y) (hw.1.trans hRr)).2.2.2 (hw.2.2.2 hm)).1
  have hh := constrainedJacobian_norm_bounds Metric.isOpen_ball huU (hUa _ huU).differentiableAt
    hmean (eps := 3/32) (by norm_num) (J.corrected_derivative_bound B phi hphi d r C R P hr hR hRr _ hu)
  norm_num at hh ⊢
  exact hh

end
end IsingBulk.Anisotropic.NegativeNormalForm
