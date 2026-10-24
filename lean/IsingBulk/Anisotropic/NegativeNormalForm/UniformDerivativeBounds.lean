import IsingBulk.Anisotropic.NegativeNormalForm.UniformNearIdentity

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology

 theorem inverse_error_difference {n : ℕ} (F : Config n → Config n) (r : ℝ)
    (hLip : LipschitzOnWith (1/64) (fun x => F x-x) (closedBall 0 r))
    (x x' y y' : Config n) (hx : ‖x‖≤r) (hx' : ‖x'‖≤r)
    (hxy : F x=y) (hxy' : F x'=y') (hb : ‖x-x'‖≤2*‖y-y'‖) :
    ‖(x-y)-(x'-y')‖≤(1/32)*‖y-y'‖ := by
  have hh := hLip.dist_le_mul x (by simpa using hx) x' (by simpa using hx')
  simp only [dist_eq_norm,hxy,hxy',NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] at hh
  have he : (y-x)-(y'-x')=-((x-y)-(x'-y')) := by abel
  rw [he,norm_neg] at hh
  nlinarith

 theorem UniformCorrectionWitness.corrected_perturbation_lipschitz {n : ℕ}
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C R : ℝ)
    (P : UniformProjectedWitness B phi hphi n d r C)
    (J : UniformCorrectionWitness B phi hphi n d r C P R) (hRr : R≤r/2) :
    LipschitzOnWith (3/32) (fun y => P.V (J.W y)-y) (closedBall 0 (R/2)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  have hy' : ‖y‖≤R/2 := by simpa using hy
  have hz' : ‖z‖≤R/2 := by simpa using hz
  have hw := J.w_inverse y hy'
  have hw' := J.w_inverse z hz'
  have hv := P.v_inverse (J.W y) (hw.1.trans hRr)
  have hv' := P.v_inverse (J.W z) (hw'.1.trans hRr)
  have hWL := J.w_lip y z hy' hz'
  have hWerr := inverse_error_difference
    (fun w => meanCorrection (actualMeanField B phi hphi d P.T P.V w) w) R J.correction_lip
    (J.W y) (J.W z) y z hw.1 hw'.1 hw.2.2.1 hw'.2.2.1 hWL
  have hVerr := inverse_error_difference
    (projectedExtension (fun v => phaseSeparableMap B phi hphi d (P.T v) v)) r P.projected_lip
    (P.V (J.W y)) (P.V (J.W z)) (J.W y) (J.W z) hv.1 hv'.1 hv.2.2.1 hv'.2.2.1
    (P.v_lip (J.W y) (J.W z) (hw.1.trans hRr) (hw'.1.trans hRr))
  have he : (P.V (J.W y)-y)-(P.V (J.W z)-z)=
      ((P.V (J.W y)-J.W y)-(P.V (J.W z)-J.W z))+((J.W y-y)-(J.W z-z)) := by abel
  have htri := norm_add_le ((P.V (J.W y)-J.W y)-(P.V (J.W z)-J.W z)) ((J.W y-y)-(J.W z-z))
  rw [← he] at htri
  simp only [dist_eq_norm,NNReal.coe_div,NNReal.coe_ofNat]
  nlinarith

 theorem UniformCorrectionWitness.corrected_derivative_bound {n : ℕ}
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C R : ℝ)
    (P : UniformProjectedWitness B phi hphi n d r C)
    (J : UniformCorrectionWitness B phi hphi n d r C P R)
    (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) (y : Config n) (hy : ‖y‖<R/2) :
    ‖fderiv ℂ (fun x => P.V (J.W x)) y-ContinuousLinearMap.id ℂ (Config n)‖≤3/32 := by
  have hnb : closedBall (0:Config n) (R/2)∈𝓝 y :=
    mem_of_superset (isOpen_ball.mem_nhds (by simpa using hy)) ball_subset_closedBall
  have hh := norm_fderiv_le_of_lipschitzOn ℂ hnb
    (J.corrected_perturbation_lipschitz B phi hphi d r C R P hRr)
  have ha := (J.corrected_bounds B phi hphi d r C R P hr hR hRr).1 y (by simpa using hy)
  change ‖fderiv ℂ ((fun x => P.V (J.W x))-id) y‖≤(3/32:ℝ) at hh
  rw [fderiv_sub ha.differentiableAt differentiableAt_id,fderiv_id] at hh
  exact hh

end
end IsingBulk.Anisotropic.NegativeNormalForm
