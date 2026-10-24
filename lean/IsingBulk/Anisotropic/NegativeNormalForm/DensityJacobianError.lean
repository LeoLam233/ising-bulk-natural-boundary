import IsingBulk.Anisotropic.NegativeNormalForm.DensityJacobianRadial

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric
open scoped Topology

/-- The actual constrained determinant differs from its central value 1 by
O(n times the squared ambient sup norm), with a dimension-independent constant. -/
theorem constrainedJacobian_quadratic_error {m : ℕ} {Phi : Config (m+1)→Config (m+1)} {r : ℝ}
    (hr : 0<r) (ha : AnalyticOnNhd ℂ Phi (ball 0 r))
    (hmean : ∀v∈ball 0 r,ZeroMean v → ZeroMean (Phi v))
    (heq : ∀e v,Phi (permute e v)=permute e (Phi v))
    (hd0 : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config (m+1))) 0)
    (hD : ∀v∈ball 0 r,‖fderiv ℂ Phi v-ContinuousLinearMap.id ℂ (Config (m+1))‖≤3/32)
    (u : Config m) (hu : ‖freeChartCLM m u‖≤r/2)
    (hsmall : 4*(m+1:ℕ)*(‖freeChartCLM m u‖/r)^2≤1) :
    ‖constrainedJacobian Phi u-1‖≤8*(m+1:ℕ)*(‖freeChartCLM m u‖/r)^2 := by
  by_cases hu0 : u=0
  · subst u
    simp [constrainedJacobian_zero Phi hd0]
  have hy0 : freeChartCLM m u≠0 := by
    intro h
    exact hu0 (freeChart_injective m (by simpa using h))
  have hn : 0<‖freeChartCLM m u‖ := norm_pos_iff.mpr hy0
  let a : ℂ := (‖freeChartCLM m u‖:ℝ)
  have ha0 : a≠0 := by dsimp [a]; exact_mod_cast hn.ne'
  have han : ‖a‖=‖freeChartCLM m u‖ := by simp [a]
  let v : Config m := a⁻¹ • u
  have hunit : ‖freeChartCLM m v‖≤1 := by
    dsimp [v]
    rw [map_smul,norm_smul,norm_inv,han,inv_mul_cancel₀ hn.ne']
  obtain ⟨L,_,_,hexp,hbound⟩ := constrainedJacobian_radial_log hr ha hmean heq hd0 hD v hunit
  have hav : a • v=u := by simp [v,smul_smul,ha0]
  have haR : a∈ball (0:ℂ) r := by
    simp only [mem_ball,dist_zero_right,han]
    exact hu.trans_lt (by linarith)
  have hLa := hbound a (by rwa [han])
  rw [han] at hLa
  have hJn : constrainedJacobian Phi u=Complex.exp (L a) := by rw [←hav]; exact (hexp a haR).symm
  rw [hJn]
  exact (Complex.norm_exp_sub_one_le (hLa.trans hsmall)).trans (by nlinarith)

/-- Uniform specialization to the actual inverse normal form Φ=V∘W. -/
theorem UniformCorrectionWitness.constrainedJacobian_error {m : ℕ}
    (B : ℂ→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C R : ℝ)
    (P : UniformProjectedWitness B phi hphi (m+1) d r C)
    (J : UniformCorrectionWitness B phi hphi (m+1) d r C P R)
    (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) (u : Config m)
    (hu : ‖freeChartCLM m u‖≤R/4)
    (hsmall : 4*(m+1:ℕ)*(‖freeChartCLM m u‖/(R/2))^2≤1) :
    ‖constrainedJacobian (fun y => P.V (J.W y)) u-1‖≤
      8*(m+1:ℕ)*(‖freeChartCLM m u‖/(R/2))^2 := by
  have hUa := (J.corrected_bounds B phi hphi d r C R P hr hR hRr).1
  have hmean : ∀y∈ball (0:Config (m+1)) (R/2),ZeroMean y → ZeroMean (P.V (J.W y)) := by
    intro y hy hm
    have hy' : ‖y‖≤R/2 := le_of_lt (by simpa using hy)
    have hw := J.w_inverse y hy'
    exact ((P.v_inverse (J.W y) (hw.1.trans hRr)).2.2.2 (hw.2.2.2 hm)).1
  have hd : HasFDerivAt (fun y => P.V (J.W y)) (ContinuousLinearMap.id ℂ (Config (m+1))) 0 := by
    have hv : HasFDerivAt P.V (ContinuousLinearMap.id ℂ (Config (m+1))) (J.W 0) := by
      rw [J.w_zero]
      exact P.v_deriv
    simpa using hv.comp 0 J.w_deriv
  exact constrainedJacobian_quadratic_error (by positivity) hUa hmean
    (fun e y => by rw [J.w_perm,P.v_perm]) hd
    (fun y hy => J.corrected_derivative_bound B phi hphi d r C R P hr hR hRr y (by simpa using hy))
    u (by convert hu using 1; ring) hsmall

end
end IsingBulk.Anisotropic.NegativeNormalForm
