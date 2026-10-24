import IsingBulk.Anisotropic.NegativeNormalForm.DensityJacobianError
import IsingBulk.Anisotropic.NegativeNormalForm.ScaledDensityCenter

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric
open scoped Topology

theorem scalarConfiguration_det {m : ℕ} (c : ℂ) :
    (scalarConfiguration (n := m) c).toLinearMap.det=c^m := by
  change LinearMap.det (c • (LinearMap.id : Config m→ₗ[ℂ]Config m))=c^m
  rw [LinearMap.det_smul,LinearMap.det_id]
  simp

theorem constrainedJacobian_scalar_input {m : ℕ} {Phi : Config (m+1)→Config (m+1)}
    (c : ℂ) (u : Config m) (hd : DifferentiableAt ℂ Phi (c • freeChartCLM m u)) :
    constrainedJacobian (fun y => Phi (c • y)) u=c^m*constrainedJacobian Phi (c • u) := by
  have he : constrainedMap (fun y => Phi (c • y))=fun v => constrainedMap Phi (scalarConfiguration c v) := by
    funext v
    change freeCoordinatesCLM m (Phi (c • freeChartCLM m v))=
      freeCoordinatesCLM m (Phi (freeChartCLM m (c • v)))
    rw [map_smul]
  have hdc : DifferentiableAt ℂ (constrainedMap Phi) (scalarConfiguration c u) :=
    constrainedMap_differentiableAt (by simpa only [scalarConfiguration,smul_apply,
      ContinuousLinearMap.id_apply,map_smul] using hd)
  have hh := hdc.hasFDerivAt.comp u ((scalarConfiguration c).hasFDerivAt (x := u))
  rw [constrainedJacobian_eq_fderiv_det,he]
  have hh' : fderiv ℂ (fun v => constrainedMap Phi (scalarConfiguration c v)) u=
      (fderiv ℂ (constrainedMap Phi) (scalarConfiguration c u)).comp (scalarConfiguration c) := by
    simpa only [Function.comp_def] using hh.fderiv
  rw [hh']
  change ((fderiv ℂ (constrainedMap Phi) (scalarConfiguration c u)).toLinearMap.comp
    (scalarConfiguration c).toLinearMap).det=c^m*constrainedJacobian Phi (c • u)
  rw [LinearMap.det_comp,scalarConfiguration_det,constrainedJacobian_eq_fderiv_det]
  exact mul_comm _ _

theorem constrainedJacobian_scalar_ratio {m : ℕ} {Phi : Config (m+1)→Config (m+1)}
    {c : ℂ} (hc : c≠0) (u : Config m)
    (hd0 : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config (m+1))) 0)
    (hd : DifferentiableAt ℂ Phi (c • freeChartCLM m u)) :
    constrainedJacobian (fun y => Phi (c • y)) u/
      constrainedJacobian (fun y => Phi (c • y)) 0=constrainedJacobian Phi (c • u) := by
  rw [constrainedJacobian_scalar_input c u hd,
    constrainedJacobian_scalar_input c 0 (by simpa using hd0.differentiableAt)]
  simp only [smul_zero,constrainedJacobian_zero Phi hd0,mul_one]
  exact mul_div_cancel_left₀ _ (pow_ne_zero m hc)

/-- The canonical scalar normalization cancels exactly from the Jacobian ratio. -/
theorem constrainedJacobian_scalar_ratio_error {m : ℕ} {Phi : Config (m+1)→Config (m+1)} {r : ℝ}
    (hr : 0<r) (ha : AnalyticOnNhd ℂ Phi (ball 0 r))
    (hmean : ∀v∈ball 0 r,ZeroMean v → ZeroMean (Phi v))
    (heq : ∀e v,Phi (permute e v)=permute e (Phi v))
    (hd0 : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config (m+1))) 0)
    (hD : ∀v∈ball 0 r,‖fderiv ℂ Phi v-ContinuousLinearMap.id ℂ (Config (m+1))‖≤3/32)
    {c : ℂ} (hc : c≠0) (u : Config m) (hu : ‖freeChartCLM m (c • u)‖≤r/2)
    (hsmall : 4*(m+1:ℕ)*(‖freeChartCLM m (c • u)‖/r)^2≤1) :
    ‖constrainedJacobian (fun y => Phi (c • y)) u/
      constrainedJacobian (fun y => Phi (c • y)) 0-1‖≤
      8*(m+1:ℕ)*(‖freeChartCLM m (c • u)‖/r)^2 := by
  have hd : DifferentiableAt ℂ Phi (c • freeChartCLM m u) := by
    apply (ha _ ?_).differentiableAt
    rw [mem_ball,dist_zero_right,←map_smul]
    exact hu.trans_lt (by linarith)
  rw [constrainedJacobian_scalar_ratio hc u hd0 hd]
  exact constrainedJacobian_quadratic_error hr ha hmean heq hd0 hD (c • u) hu hsmall

end
end IsingBulk.Anisotropic.NegativeNormalForm
