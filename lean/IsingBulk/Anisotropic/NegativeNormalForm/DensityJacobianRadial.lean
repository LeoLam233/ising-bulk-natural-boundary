import IsingBulk.Anisotropic.NegativeNormalForm.DensityJacobianLog

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators

theorem constrainedJacobian_analyticAt_of {m : ℕ} (Phi : Config (m+1)→Config (m+1)) {u : Config m}
    (hPhi : AnalyticAt ℂ Phi (freeChartCLM m u)) : AnalyticAt ℂ (constrainedJacobian Phi) u := by
  have hC : AnalyticAt ℂ (constrainedMap Phi) u :=
    ((freeCoordinatesCLM m).analyticAt _).comp (hPhi.comp ((freeChartCLM m).analyticAt u))
  have hD := hC.fderiv
  have hentry (i j : Fin m) : AnalyticAt ℂ
      (fun w => fderiv ℂ (constrainedMap Phi) w (Pi.single j 1) i) u := by
    let L : (Config m→L[ℂ]Config m)→L[ℂ]Config m := ContinuousLinearMap.apply ℂ (Config m) (Pi.single j 1)
    exact (analyticAt_pi_iff.mp ((L.analyticAt _).comp hD)) i
  have he : constrainedJacobian Phi=fun w => ∑e : Equiv.Perm (Fin m),
      (Equiv.Perm.sign e:ℂ)*∏i,fderiv ℂ (constrainedMap Phi) w (Pi.single i 1) (e i) := by
    funext w
    exact Matrix.det_apply' _
  rw [he]
  apply Finset.analyticAt_fun_sum
  intro e _
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_prod
  intro i _
  exact hentry _ _

/-- Radial normalized logarithm of the actual constrained determinant. Its
quadratic bound is linear, rather than quadratic, in the particle dimension. -/
theorem constrainedJacobian_radial_log {m : ℕ} {Phi : Config (m+1)→Config (m+1)} {r : ℝ}
    (hr : 0<r) (ha : AnalyticOnNhd ℂ Phi (ball 0 r))
    (hmean : ∀v∈ball 0 r,ZeroMean v → ZeroMean (Phi v))
    (heq : ∀e v,Phi (permute e v)=permute e (Phi v))
    (hd0 : HasFDerivAt Phi (ContinuousLinearMap.id ℂ (Config (m+1))) 0)
    (hD : ∀v∈ball 0 r,‖fderiv ℂ Phi v-ContinuousLinearMap.id ℂ (Config (m+1))‖≤3/32)
    (u : Config m) (hu : ‖freeChartCLM m u‖≤1) :
    ∃L : ℂ→ℂ,AnalyticOnNhd ℂ L (ball 0 r) ∧ L 0=0 ∧
      (∀z∈ball 0 r,Complex.exp (L z)=constrainedJacobian Phi (z • u)) ∧
      ∀z : ℂ,‖z‖≤r/2 → ‖L z‖≤4*(m+1:ℕ)*(‖z‖/r)^2 := by
  let f : ℂ→ℂ := fun z => constrainedJacobian Phi (z • u)
  have hpoint (z : ℂ) (hz : z∈ball 0 r) : freeChartCLM m (z • u)∈ball 0 r := by
    simp only [mem_ball,dist_zero_right,map_smul,norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg z) hu).trans_lt (by simpa using hz)
  have hf : AnalyticOnNhd ℂ f (ball 0 r) := by
    intro z hz
    exact (constrainedJacobian_analyticAt_of Phi (ha _ (hpoint z hz))).comp (f := fun w : ℂ => w • u)
      (analyticAt_id.smul analyticAt_const)
  have hf0 : f 0=1 := by simp [f,constrainedJacobian_zero Phi hd0]
  have hJ0 : HasFDerivAt (constrainedJacobian Phi) (0 : Config m→L[ℂ]ℂ) (0:Config m) := by
    rw [←constrainedJacobian_fderiv_zero hr ha hmean heq]
    exact (constrainedJacobian_analyticAt Phi (ha 0 (mem_ball_self hr))).differentiableAt.hasFDerivAt
  have hJ0' : HasFDerivAt (constrainedJacobian Phi) (0 : Config m→L[ℂ]ℂ) ((0:ℂ) • u) := by simpa using hJ0
  have hdf : deriv f 0=0 := by
    simpa [f,Function.comp_def] using! (hJ0'.comp_hasDerivAt (0:ℂ) ((hasDerivAt_id (0:ℂ)).smul_const u)).deriv
  have hbounds (z : ℂ) (hz : z∈ball 0 r) :
      (29/32:ℝ)^m≤‖f z‖ ∧ ‖f z‖≤(35/32:ℝ)^m := by
    have hh := constrainedJacobian_norm_bounds isOpen_ball (hpoint z hz) (ha _ (hpoint z hz)).differentiableAt
      hmean (eps := 3/32) (by norm_num) (hD _ (hpoint z hz))
    norm_num at hh ⊢
    exact hh
  have hn (z : ℂ) (hz : z∈ball 0 r) : f z≠0 := by
    intro he
    have hh := (hbounds z hz).1
    rw [he,norm_zero] at hh
    exact (not_le_of_gt (pow_pos (by norm_num : (0:ℝ)<29/32) m)) hh
  have hb (z : ℂ) (hz : z∈ball 0 r) : ‖f z‖≤Real.exp (m+1:ℕ) := by
    have hbase : (35/32:ℝ)≤Real.exp 1 := by nlinarith [Real.add_one_le_exp (1:ℝ)]
    calc
      ‖f z‖≤(35/32:ℝ)^m := (hbounds z hz).2
      _≤(Real.exp 1)^m := pow_le_pow_left₀ (by norm_num) hbase _
      _=Real.exp (m:ℝ) := by rw [←Real.exp_nat_mul]; simp
      _≤Real.exp (m+1:ℕ) := Real.exp_le_exp.mpr (by norm_num)
  exact analytic_log_quadratic_bound hr (by positivity : (0:ℝ)<(m+1:ℕ)) hf hf0 hdf hn hb

end
end IsingBulk.Anisotropic.NegativeNormalForm
