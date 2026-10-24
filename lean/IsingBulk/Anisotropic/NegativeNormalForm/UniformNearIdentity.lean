import IsingBulk.Anisotropic.NegativeNormalForm.UniformCorrectionInverse

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric

 theorem inverse_error_from_small_perturbation {n : ℕ} (F : Config n → Config n)
    (r : ℝ) (hr : 0≤r) (hF0 : F 0=0)
    (hLip : LipschitzOnWith (1/64) (fun x => F x-x) (closedBall 0 r))
    (x y : Config n) (hx : ‖x‖≤r) (hxy : F x=y) (hb : ‖x‖≤2*‖y‖) :
    ‖x-y‖≤(1/32)*‖y‖ := by
  have hh := hLip.dist_le_mul x (by simpa using hx) 0 (by simpa using hr)
  simp only [dist_eq_norm,hF0,hxy,sub_self,sub_zero,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] at hh
  rw [norm_sub_rev] at hh
  nlinarith

 theorem UniformCorrectionWitness.inverse_error {n : ℕ}
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C R : ℝ)
    (P : UniformProjectedWitness B phi hphi n d r C)
    (J : UniformCorrectionWitness B phi hphi n d r C P R) (hR : 0≤R)
    (y : Config n) (hy : ‖y‖≤R/2) : ‖J.W y-y‖≤(1/32)*‖y‖ := by
  have hw := J.w_inverse y hy
  exact inverse_error_from_small_perturbation
    (fun w => meanCorrection (actualMeanField B phi hphi d P.T P.V w) w) R hR
    (meanCorrection_zero_along (actualMeanField B phi hphi d P.T P.V))
    J.correction_lip (J.W y) y hw.1 hw.2.2.1 hw.2.1

 theorem UniformProjectedWitness.inverse_error {n : ℕ}
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C : ℝ)
    (P : UniformProjectedWitness B phi hphi n d r C) (hr : 0≤r)
    (y : Config n) (hy : ‖y‖≤r/2) : ‖P.V y-y‖≤(1/32)*‖y‖ := by
  have hv := P.v_inverse y hy
  have hF0 := projectedExtension_zero (fun x => phaseSeparableMap B phi hphi d (P.T x) x)
    (phaseSeparableMap_zero_equivariant_aux B phi hphi d (P.T 0))
  exact inverse_error_from_small_perturbation _ r hr hF0 P.projected_lip (P.V y) y hv.1 hv.2.2.1 hv.2.1

/-- The full actual corrected inverse is uniformly close enough to the identity
for the extended straight complex homotopy. -/
theorem UniformCorrectionWitness.corrected_bounds {n : ℕ}
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d : ℂ) (r C R : ℝ)
    (P : UniformProjectedWitness B phi hphi n d r C)
    (J : UniformCorrectionWitness B phi hphi n d r C P R)
    (hr : 0<r) (hR : 0<R) (hRr : R≤r/2) :
    AnalyticOnNhd ℂ (fun y => P.V (J.W y)) (ball 0 (R/2)) ∧
      (∀ y, ‖y‖≤R/2 → ‖P.V (J.W y)‖≤4*‖y‖ ∧ ‖P.V (J.W y)-y‖≤(3/32)*‖y‖) := by
  refine ⟨?_,?_⟩
  · intro y hy
    have hy' : ‖y‖<R/2 := by simpa using hy
    have hw := J.w_inverse y hy'.le
    have hwy : ‖J.W y‖<r/2 := by linarith [hw.2.1]
    exact (P.v_analytic (J.W y) (by simpa using hwy)).comp (f := J.W) (J.w_analytic y hy)
  · intro y hy
    have hw := J.w_inverse y hy
    have hv := P.v_inverse (J.W y) (hw.1.trans hRr)
    have hve := P.inverse_error B phi hphi d r C hr.le (J.W y) (hw.1.trans hRr)
    have hwe := J.inverse_error B phi hphi d r C R P hR.le y hy
    refine ⟨by nlinarith [hv.2.1,hw.2.1],?_⟩
    have hh := norm_add_le (P.V (J.W y)-J.W y) (J.W y-y)
    rw [sub_add_sub_cancel] at hh
    nlinarith [hw.2.1]

end
end IsingBulk.Anisotropic.NegativeNormalForm
