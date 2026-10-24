import IsingBulk.Anisotropic.NegativeNormalForm.DensityJacobianLinear

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators

theorem zeroMean_permute {n : ℕ} (e : Equiv.Perm (Fin n)) {v : Config n} (hv : ZeroMean v) :
    ZeroMean (permute e v) := by
  change ∑i,v (e i)=0
  rw [Equiv.sum_comp e v]
  exact hv

def freePermutation {m : ℕ} (e : Equiv.Perm (Fin (m+1))) : Config m→L[ℂ]Config m :=
  (freeCoordinatesCLM m).comp ((permuteCLM e).comp (freeChartCLM m))

theorem freeChart_freePermutation {m : ℕ} (e : Equiv.Perm (Fin (m+1))) (u : Config m) :
    freeChartCLM m (freePermutation e u)=permute e (freeChartCLM m u) :=
  freeChart_freeCoordinates (zeroMean_permute e (freeChartCLM_zeroMean m u))

theorem freePermutation_injective {m : ℕ} (e : Equiv.Perm (Fin (m+1))) :
    Function.Injective (freePermutation e) := by
  intro u v h
  apply freeChart_injective m
  have hh := congrArg (freeChartCLM m) h
  rw [freeChart_freePermutation,freeChart_freePermutation] at hh
  funext i
  simpa [permute] using congrFun hh (e.symm i)

theorem freePermutation_det_ne_zero {m : ℕ} (e : Equiv.Perm (Fin (m+1))) :
    (freePermutation e).toLinearMap.det≠0 := by
  intro h
  have hk : LinearMap.ker (freePermutation e).toLinearMap=⊥ := LinearMap.ker_eq_bot.mpr (freePermutation_injective e)
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) hk

theorem freePermutation_swap_single {m : ℕ} (i : Fin m) :
    freePermutation (Equiv.swap i.castSucc (Fin.last m)) (Pi.single i (1:ℂ))= -Pi.single i 1 := by
  ext j
  change freeChartCLM m (Pi.single i 1) ((Equiv.swap i.castSucc (Fin.last m)) j.castSucc)= -((Pi.single i (1:ℂ) : Config m) j)
  by_cases hji : j=i
  · subst j
    simp
  · have hc : j.castSucc≠i.castSucc := by simpa using hji
    rw [Equiv.swap_apply_of_ne_of_ne hc (Fin.castSucc_ne_last j),freeChartCLM_castSucc]
    simp [hji]

theorem constrainedJacobian_eq_fderiv_det {m : ℕ} (Phi : Config (m+1)→Config (m+1)) (u : Config m) :
    constrainedJacobian Phi u=(fderiv ℂ (constrainedMap Phi) u).toLinearMap.det := by
  unfold constrainedJacobian
  rw [←LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin m))]
  congr 1


theorem constrainedMap_differentiableAt {m : ℕ} {Phi : Config (m+1)→Config (m+1)} {u : Config m}
    (hd : DifferentiableAt ℂ Phi (freeChartCLM m u)) : DifferentiableAt ℂ (constrainedMap Phi) u :=
  (freeCoordinatesCLM m).differentiableAt.comp u (hd.comp u (freeChartCLM m).differentiableAt)

theorem constrainedJacobian_freePermutation {m : ℕ} {Phi : Config (m+1)→Config (m+1)}
    {U : Set (Config (m+1))} (hU : IsOpen U) {u : Config m} (hu : freeChartCLM m u∈U)
    (hmean : ∀v∈U,ZeroMean v → ZeroMean (Phi v))
    (heq : ∀e v,Phi (permute e v)=permute e (Phi v))
    (e : Equiv.Perm (Fin (m+1)))
    (hd : DifferentiableAt ℂ Phi (freeChartCLM m u))
    (hd' : DifferentiableAt ℂ Phi (permute e (freeChartCLM m u))) :
    constrainedJacobian Phi (freePermutation e u)=constrainedJacobian Phi u := by
  have hdc := constrainedMap_differentiableAt hd
  have hdc' : DifferentiableAt ℂ (constrainedMap Phi) (freePermutation e u) :=
    constrainedMap_differentiableAt (by rwa [freeChart_freePermutation])
  have hf : (fun w => constrainedMap Phi (freePermutation e w))=ᶠ[𝓝 u]
      (fun w => freePermutation e (constrainedMap Phi w)) := by
    filter_upwards [(freeChartCLM m).continuous.continuousAt.eventually (hU.mem_nhds hu)] with w hw
    change freeCoordinatesCLM m (Phi (freeChartCLM m (freePermutation e w)))=
      freeCoordinatesCLM m (permute e (freeChartCLM m (freeCoordinatesCLM m (Phi (freeChartCLM m w)))))
    rw [freeChart_freePermutation,heq,freeChart_freeCoordinates (hmean _ hw (freeChartCLM_zeroMean m w))]
  have h1 := hdc'.hasFDerivAt.comp u ((freePermutation e).hasFDerivAt (x := u))
  have h2 := ((freePermutation e).hasFDerivAt (x := constrainedMap Phi u)).comp u hdc.hasFDerivAt
  have he := (h1.congr_of_eventuallyEq hf.symm).unique h2
  have hh := congrArg (fun L : Config m→L[ℂ]Config m => L.toLinearMap.det) he
  change ((fderiv ℂ (constrainedMap Phi) (freePermutation e u)).toLinearMap.comp (freePermutation e).toLinearMap).det=
    ((freePermutation e).toLinearMap.comp (fderiv ℂ (constrainedMap Phi) u).toLinearMap).det at hh
  rw [LinearMap.det_comp,LinearMap.det_comp,mul_comm (freePermutation e).toLinearMap.det] at hh
  rw [constrainedJacobian_eq_fderiv_det,constrainedJacobian_eq_fderiv_det]
  exact mul_right_cancel₀ (freePermutation_det_ne_zero e) hh

/-- Permutation symmetry kills the entire first variation of the constrained
Jacobian at zero: swapping one free coordinate with the last negates its basis vector. -/
theorem constrainedJacobian_fderiv_zero {m : ℕ} {Phi : Config (m+1)→Config (m+1)} {r : ℝ}
    (hr : 0<r) (ha : AnalyticOnNhd ℂ Phi (ball 0 r))
    (hmean : ∀v∈ball 0 r,ZeroMean v → ZeroMean (Phi v))
    (heq : ∀e v,Phi (permute e v)=permute e (Phi v)) :
    fderiv ℂ (constrainedJacobian Phi) 0=0 := by
  have h0 : (0:Config (m+1))∈ball 0 r := mem_ball_self hr
  have hj := (constrainedJacobian_analyticAt Phi (ha 0 h0)).differentiableAt
  have hlin (e : Equiv.Perm (Fin (m+1))) :
      (fderiv ℂ (constrainedJacobian Phi) 0).comp (freePermutation e)=fderiv ℂ (constrainedJacobian Phi) 0 := by
    have hevent : (fun w => constrainedJacobian Phi (freePermutation e w))=ᶠ[𝓝 (0:Config m)] constrainedJacobian Phi := by
      have ht : Tendsto (freeChartCLM m) (𝓝 0) (𝓝 0) := by simpa using (freeChartCLM m).continuous.tendsto 0
      filter_upwards [ht.eventually (Metric.ball_mem_nhds (0:Config (m+1)) hr)] with w hw
      apply constrainedJacobian_freePermutation isOpen_ball hw hmean heq e (ha _ hw).differentiableAt
      apply (ha _ ?_).differentiableAt
      simpa only [mem_ball,dist_zero_right,norm_permute] using hw
    have hj' : HasFDerivAt (constrainedJacobian Phi) (fderiv ℂ (constrainedJacobian Phi) 0) (freePermutation e 0) := by simpa using hj.hasFDerivAt
    have hcomp := hj'.comp (0:Config m) ((freePermutation e).hasFDerivAt (x := 0))
    simpa only [map_zero] using (hcomp.congr_of_eventuallyEq hevent.symm).unique hj.hasFDerivAt
  have hmap : (fderiv ℂ (constrainedJacobian Phi) 0).toLinearMap=0 := by
    apply (Pi.basisFun ℂ (Fin m)).ext
    intro i
    have hh := congrArg (fun L : Config m→L[ℂ]ℂ => L (Pi.single i 1))
      (hlin (Equiv.swap i.castSucc (Fin.last m)))
    simp only [ContinuousLinearMap.comp_apply,freePermutation_swap_single,map_neg] at hh
    have hh0 : (fderiv ℂ (constrainedJacobian Phi) 0) (Pi.single i 1)=0 := by linear_combination -hh/2
    simpa using hh0
  ext v
  exact congrArg (fun L : Config m→ₗ[ℂ]ℂ => L v) hmap

end
end IsingBulk.Anisotropic.NegativeNormalForm
