import IsingBulk.Analysis.BranchCone

/-! Attenuation on the actual logarithmic branch, allowing a displaced center. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology

theorem sqrt_negative_cone_of_real_margin (H : ℂ) (hi : H.im < 0)
    (hr : H.re ≤ (1/50:ℝ)*‖H‖) :
    (7/10:ℝ)*‖Complex.sqrt H‖ ≤ -(Complex.sqrt H).im := by
  obtain ⟨_,hcomp⟩ := sqrt_lower_components H hi
  obtain ⟨_,hsim⟩ := sqrt_lower_orientation H hi
  have hsq : ‖Complex.sqrt H‖^2 = ‖H‖ := by rw [← norm_pow,sqrt_sq]
  have hsqim : (-(Complex.sqrt H).im)^2 = (‖H‖-H.re)/2 := by
    rw [hcomp,Real.sq_sqrt (by linarith [norm_nonneg H])]
  nlinarith [norm_nonneg (Complex.sqrt H)]

theorem logarithmic_attenuation (W : ℂ) (hre : 0 < W.re) (him : 0 < W.im)
    (hsector : (1-W^2).re ≤ (1/50:ℝ)*‖1-W^2‖)
    (hsmall : ‖1-W^2‖ ≤ (1/100:ℝ))
    (hD : ‖1-W‖ ≤ ‖1-W^2‖) :
    (3/10:ℝ)*Real.sqrt ‖1-W^2‖ ≤ -(lowerArccos W).im := by
  let H := 1-W^2
  let S := Complex.sqrt H
  have hHi : H.im < 0 := by dsimp [H]; simp [pow_two,Complex.mul_im]; nlinarith [mul_pos hre him]
  have hcone := sqrt_negative_cone_of_real_margin H hHi hsector
  have hsq : ‖S‖^2 = ‖H‖ := by rw [← norm_pow,sqrt_sq]
  have hsn : 0 ≤ ‖S‖ := norm_nonneg _
  have hs : ‖S‖ ≤ (1/10:ℝ) := by nlinarith
  have hDsmall : ‖1-W‖ ≤ ‖S‖/10 := by
    have hx : ‖S‖^2 ≤ ‖S‖/10 := by nlinarith
    nlinarith
  have hrootre : 1+(3/5:ℝ)*‖S‖ ≤ (inverseCosineRoot W).re := by
    have hreal := Complex.re_le_norm (1-W)
    simp only [Complex.sub_re,Complex.one_re] at hreal
    change (7/10:ℝ)*‖S‖ ≤ -S.im at hcone
    change 1+(3/5:ℝ)*‖S‖ ≤ (W+Complex.I*S).re
    simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub]
    linarith
  have hrootlo : 1+(3/5:ℝ)*‖S‖ ≤ ‖inverseCosineRoot W‖ := hrootre.trans (Complex.re_le_norm _)
  have hrootup : ‖inverseCosineRoot W‖ ≤ 2 := by
    have hW : ‖W‖ ≤ 1+‖1-W‖ := by
      have h := norm_sub_le (1:ℂ) (1-W)
      simpa using h
    have hz := norm_add_le W (Complex.I*S)
    simp only [norm_mul,Complex.norm_I,one_mul] at hz
    change ‖W+Complex.I*S‖ ≤ 2
    nlinarith
  have hp : 0 < ‖inverseCosineRoot W‖ := norm_pos_iff.mpr (inverseCosineRoot_ne_zero W)
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have hlog' : (‖inverseCosineRoot W‖-1)/‖inverseCosineRoot W‖ ≤ Real.log ‖inverseCosineRoot W‖ := by
    convert hlog using 1
    field_simp
  have hlo : (3/10:ℝ)*‖S‖ ≤ Real.log ‖inverseCosineRoot W‖ := by
    apply le_trans _ hlog'
    apply (le_div_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hrootup hsn]
  have hnorm : Real.sqrt ‖H‖ = ‖S‖ := by rw [← hsq,Real.sqrt_sq hsn]
  change (3/10:ℝ)*Real.sqrt ‖H‖ ≤ -(lowerArccos W).im
  rw [hnorm]
  simpa [lowerArccos,Complex.mul_im,Complex.log_re] using hlo

theorem factor_real_upper (D : ℂ) (u Q a K C : ℝ) (ha : 0 ≤ a) (hu : u ≤ 0)
    (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (hr : |D.re-a*u| ≤ K*(u^2+Q^2)) (hn : ‖D‖ ≤ C*(|u|+Q)) :
    (D*(2-D)).re ≤ (2*K+C^2)*(|u|+Q)^2 := by
  have hRe : D.re ≤ a*u+K*(u^2+Q^2) := by
    have h := (abs_le.mp hr).2
    linarith
  have hn' : ‖D‖^2 ≤ C^2*(|u|+Q)^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg D) hn 2
    nlinarith
  have hsum : ‖D‖^2 = D.re^2+D.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
  have hface : (D*(2-D)).re = 2*D.re-D.re^2+D.im^2 := by simp [Complex.mul_re]; ring
  rw [hface]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hu,
    mul_nonneg hK (mul_nonneg (abs_nonneg u) hQ),sq_nonneg D.re,sq_abs u]

theorem current_negative_factor_margin (d : LocalBranchData) (η : ℝ) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε t u : ℝ,
      0 < ε → ε < r → 0 ≤ t → t < r → u ≤ 0 → |u| < r →
      (1-(currentW d ε t u)^2).re ≤ η*‖1-(currentW d ε t u)^2‖ := by
  obtain ⟨c,C,r₁,hc,hC,hr₁,hmod⟩ := current_modulus_Q d
  obtain ⟨K,r₂,hK,hr₂,hreal⟩ := current_real_remainder d
  obtain ⟨r₃,hr₃,hfac⟩ := Metric.eventually_nhds_iff.mp (current_factors_near_zero d)
  let A := 2*K+C^2
  have hA : 0 < A := by dsimp [A]; positivity
  let r := min r₁ (min r₂ (min r₃ (η*c/(A*(2+d.tau)))))
  have hτ := d.tau_pos
  refine ⟨r,by dsimp [r]; positivity,?_⟩
  intro ε t u hε hεr ht htr hu hur
  have hr₁' : r ≤ r₁ := min_le_left _ _
  have hr₂' : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hr₃' : r ≤ r₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrA : r ≤ η*c/(A*(2+d.tau)) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hm,hm'⟩ := hmod ε t u hε (hεr.trans_le hr₁') ht (htr.trans_le hr₁') (hur.trans_le hr₁')
  have hre := hreal ε t u hε.le (hεr.trans_le hr₂') ht (htr.trans_le hr₂') (hur.trans_le hr₂')
  have hz : dist (ε,t,u) (0:ℝ × ℝ × ℝ) < r₃ := by
    simpa [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,abs_of_pos hε,abs_of_nonneg ht]
      using And.intro (hεr.trans_le hr₃') (And.intro (htr.trans_le hr₃') (hur.trans_le hr₃'))
  have hf := (hfac hz).2.2.1
  have hupper := factor_real_upper (currentD d ε t u) u (ε+d.tau*t) d.a K C
    d.a_pos.le hu (by positivity) hK.le hre (by simpa [add_assoc] using hm')
  have hAL : A*(|u|+ε+d.tau*t) ≤ η*c := by
    have hv := (le_div_iff₀ (mul_pos hA (by positivity : 0 < 2+d.tau))).mp hrA
    nlinarith [mul_le_mul_of_nonneg_left (by nlinarith [mul_lt_mul_of_pos_left htr hτ] :
      |u|+ε+d.tau*t ≤ (2+d.tau)*r) hA.le]
  have hH : c*(|u|+ε+d.tau*t) ≤ ‖currentD d ε t u*(2-currentD d ε t u)‖ := by
    rw [norm_mul]
    nlinarith [mul_le_mul_of_nonneg_left hf (norm_nonneg (currentD d ε t u))]
  have he : 1-(currentW d ε t u)^2 = currentD d ε t u*(2-currentD d ε t u) := by
    dsimp [currentD]; ring
  rw [he]
  have hL : 0 ≤ |u|+ε+d.tau*t := by positivity
  have habs := mul_le_mul_of_nonneg_right hAL hL
  have hηH := mul_le_mul_of_nonneg_left hH hη.le
  dsimp [A] at hAL habs
  nlinarith

theorem current_negative_attenuation_Q (d : LocalBranchData) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ ε t u : ℝ,
      0 < ε → ε < r → 0 ≤ t → t < r → u ≤ 0 → |u| < r →
      c*Real.sqrt (|u|+ε+d.tau*t) ≤ -(currentPhase d ε t u).im := by
  obtain ⟨c,C,r₁,hc,hC,hr₁,hmod⟩ := current_modulus_Q d
  obtain ⟨r₂,hr₂,hmargin⟩ := current_negative_factor_margin d (1/50) (by norm_num)
  obtain ⟨r₃,hr₃,hbranch⟩ := current_branch_inclusion d
  obtain ⟨r₄,hr₄,hfac⟩ := Metric.eventually_nhds_iff.mp (current_factors_near_zero d)
  let r := min r₁ (min r₂ (min r₃ (min r₄ (1/(300*C*(2+d.tau))))))
  have hτ := d.tau_pos
  refine ⟨(3/10)*Real.sqrt c,r,by positivity,by dsimp [r]; positivity,?_⟩
  intro ε t u hε hεr ht htr hu hur
  have hr₁' : r ≤ r₁ := min_le_left _ _
  have hr₂' : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hr₃' : r ≤ r₃ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr₄' : r ≤ r₄ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hrsmall : r ≤ 1/(300*C*(2+d.tau)) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hm,hm'⟩ := hmod ε t u hε (hεr.trans_le hr₁') ht (htr.trans_le hr₁') (hur.trans_le hr₁')
  have hs := hmargin ε t u hε (hεr.trans_le hr₂') ht (htr.trans_le hr₂') hu (hur.trans_le hr₂')
  obtain ⟨hre,him⟩ := hbranch ε t u hε (hεr.trans_le hr₃') ht (htr.trans_le hr₃') (hur.trans_le hr₃')
  have hz : dist (ε,t,u) (0:ℝ × ℝ × ℝ) < r₄ := by
    simpa [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,abs_of_pos hε,abs_of_nonneg ht]
      using And.intro (hεr.trans_le hr₄') (And.intro (htr.trans_le hr₄') (hur.trans_le hr₄'))
  obtain ⟨_,_,hf,hf'⟩ := hfac hz
  have he : 1-(currentW d ε t u)^2 = currentD d ε t u*(2-currentD d ε t u) := by
    dsimp [currentD]; ring
  have hDn : ‖currentD d ε t u‖ ≤ ‖1-(currentW d ε t u)^2‖ := by
    rw [he,norm_mul]
    nlinarith [mul_le_mul_of_nonneg_left hf (norm_nonneg (currentD d ε t u))]
  have hupper : ‖1-(currentW d ε t u)^2‖ ≤ 3*C*(|u|+ε+d.tau*t) := by
    rw [he,norm_mul]
    nlinarith [mul_le_mul hm' hf' (norm_nonneg _) (by positivity : 0 ≤ C*(|u|+ε+d.tau*t))]
  have hsmall : ‖1-(currentW d ε t u)^2‖ ≤ (1/100:ℝ) := by
    have hb := (le_div_iff₀ (by positivity : 0 < 300*C*(2+d.tau))).mp hrsmall
    have hL : |u|+ε+d.tau*t ≤ (2+d.tau)*r := by nlinarith [mul_lt_mul_of_pos_left htr hτ]
    nlinarith [mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 300*C)]
  have hl := logarithmic_attenuation _ hre him hs hsmall hDn
  have hsqrt := Real.sqrt_le_sqrt (hm.trans hDn)
  rw [Real.sqrt_mul hc.le] at hsqrt
  change (3/10)*Real.sqrt c*Real.sqrt (|u|+ε+d.tau*t) ≤ -(lowerArccos (currentW d ε t u)).im
  linarith

theorem current_negative_attenuation (d : LocalBranchData) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ ε t u : ℝ,
      0 < ε → ε < r → 0 ≤ t → t < r → u ≤ 0 → |u| < r →
      c*Real.sqrt (|u|+ε+t) ≤ -(currentPhase d ε t u).im := by
  obtain ⟨c,r,hc,hr,h⟩ := current_negative_attenuation_Q d
  have hmin : 0 < min 1 d.tau := lt_min zero_lt_one d.tau_pos
  refine ⟨c*Real.sqrt (min 1 d.tau),r,by positivity,hr,?_⟩
  intro ε t u hε hεr ht htr hu hur
  have hl := h ε t u hε hεr ht htr hu hur
  have hscale : min 1 d.tau*(|u|+ε+t) ≤ |u|+ε+d.tau*t := by
    nlinarith [mul_le_mul_of_nonneg_right (min_le_left 1 d.tau) (abs_nonneg u),
      mul_le_mul_of_nonneg_right (min_le_left 1 d.tau) hε.le,
      mul_le_mul_of_nonneg_right (min_le_right 1 d.tau) ht]
  have hs := Real.sqrt_le_sqrt hscale
  rw [Real.sqrt_mul hmin.le] at hs
  nlinarith [mul_le_mul_of_nonneg_left hs hc.le]

theorem original_negative_attenuation (d : LocalBranchData) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ ε u : ℝ,
      0 < ε → ε < r → u ≤ 0 → |u| < r →
      c*Real.sqrt (|u|+ε) ≤ -(originalPhase d ε u).im := by
  obtain ⟨c,r,hc,hr,h⟩ := current_negative_attenuation d
  refine ⟨c,r,hc,hr,?_⟩
  intro ε u hε hεr hu hur
  change c*Real.sqrt (|u|+ε) ≤ -(currentPhase d ε 0 u).im
  simpa only [add_zero] using h ε 0 u hε hεr le_rfl hr hu hur

end
end IsingBulk.Branch
