import IsingBulk.Analysis.BranchMagnitude

/-! Algebraic sector transfer for the actual derivative. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology ComplexConjugate

theorem sqrt_cone_of_real_margin (H : ℂ) (hi : H.im < 0)
    (hr : -(1/50:ℝ)*‖H‖ ≤ H.re) :
    (7/10:ℝ)*‖Complex.sqrt H‖ ≤ (Complex.sqrt H).re := by
  obtain ⟨hcomp,_⟩ := sqrt_lower_components H hi
  obtain ⟨hsre,_⟩ := sqrt_lower_orientation H hi
  have hsq : ‖Complex.sqrt H‖^2 = ‖H‖ := by rw [← norm_pow,sqrt_sq]
  have hsqre : (Complex.sqrt H).re^2 = (‖H‖+H.re)/2 := by
    rw [hcomp,Real.sq_sqrt (by linarith [norm_nonneg H])]
  nlinarith [norm_nonneg (Complex.sqrt H)]

theorem quotient_two_thirds_cone (U S : ℂ) (a : ℝ) (ha : 0 < a)
    (hS : S ≠ 0) (hcone : (7/10:ℝ)*‖S‖ ≤ S.re)
    (herr : ‖U-(a:ℂ)‖ ≤ a/100) :
    (2/3:ℝ)*‖U/S‖ ≤ (U/S).re := by
  have hn : 0 < ‖S‖ := norm_pos_iff.mpr hS
  have hnS : Complex.normSq S = ‖S‖^2 := (Complex.sq_norm S).symm
  have hure : a*S.re-‖U-(a:ℂ)‖*‖S‖ ≤ (U*(conj S)).re := by
    have hb := (neg_le_abs ((U-(a:ℂ))*(conj S)).re).trans
      (Complex.abs_re_le_norm ((U-(a:ℂ))*(conj S)))
    rw [norm_mul,Complex.norm_conj] at hb
    have he : ((U-(a:ℂ))*(conj S)).re = (U*(conj S)).re-a*S.re := by
      simp [Complex.mul_re]
      ring
    rw [he] at hb
    linarith
  have hdiv : (U/S).re = (U*(conj S)).re/‖S‖^2 := by
    rw [Complex.div_re,hnS]
    simp [Complex.mul_re]
    ring
  have hnum : (69/100:ℝ)*a*‖S‖ ≤ (U*(conj S)).re := by
    nlinarith [mul_le_mul_of_nonneg_left hcone ha.le,
      mul_le_mul_of_nonneg_right herr hn.le]
  have hv : (69/100:ℝ)*a ≤ (U/S).re*‖S‖ := by
    rw [hdiv]
    have he : (U*(conj S)).re/‖S‖^2*‖S‖ = (U*(conj S)).re/‖S‖ := by
      field_simp
    rw [he]
    exact (le_div_iff₀ hn).mpr hnum
  have hu : ‖U‖ ≤ (101/100:ℝ)*a := by
    have h' := norm_add_le (U-(a:ℂ)) (a:ℂ)
    rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha] at h'
    linarith
  have hnorm : ‖U/S‖*‖S‖ = ‖U‖ := by rw [norm_div,div_mul_cancel₀ _ hn.ne']
  nlinarith

theorem factor_real_lower (D : ℂ) (u Q a K C : ℝ) (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hQ : 0 ≤ Q) (hK : 0 ≤ K) (_hC : 0 ≤ C)
    (hr : |D.re-a*u| ≤ K*(u^2+Q^2)) (hn : ‖D‖ ≤ C*(u+Q)) :
    -(2*K+C^2)*(u+Q)^2 ≤ (D*(2-D)).re := by
  have hRe : a*u-K*(u^2+Q^2) ≤ D.re := by
    have h := (abs_le.mp hr).1
    linarith
  have hn' : ‖D‖^2 ≤ C^2*(u+Q)^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg D) hn 2
    nlinarith
  have hsum : ‖D‖^2 = D.re^2+D.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
  have hface : (D*(2-D)).re = 2*D.re-D.re^2+D.im^2 := by simp [Complex.mul_re]; ring
  rw [hface]
  nlinarith [mul_nonneg ha hu,mul_nonneg hK (mul_nonneg hu hQ),sq_nonneg D.im]

theorem current_positive_factor_margin (d : LocalBranchData) (η : ℝ) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε t u : ℝ,
      0 < ε → ε < r → 0 ≤ t → t < r → 0 ≤ u → u < r →
      -η*‖1-(currentW d ε t u)^2‖ ≤ (1-(currentW d ε t u)^2).re := by
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
  obtain ⟨hm,hm'⟩ := hmod ε t u hε (hεr.trans_le hr₁') ht (htr.trans_le hr₁')
    (by simpa [abs_of_nonneg hu] using hur.trans_le hr₁')
  have hre := hreal ε t u hε.le (hεr.trans_le hr₂') ht (htr.trans_le hr₂')
    (by simpa [abs_of_nonneg hu] using hur.trans_le hr₂')
  have hz : dist (ε,t,u) (0:ℝ × ℝ × ℝ) < r₃ := by
    simpa [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,abs_of_pos hε,abs_of_nonneg ht,abs_of_nonneg hu]
      using And.intro (hεr.trans_le hr₃') (And.intro (htr.trans_le hr₃') (hur.trans_le hr₃'))
  have hf := (hfac hz).2.2.1
  simp only [abs_of_nonneg hu] at hm hm'
  have hlower := factor_real_lower (currentD d ε t u) u (ε+d.tau*t) d.a K C
    d.a_pos.le hu (by positivity) hK.le hC.le hre (by simpa [add_assoc] using hm')
  have hAL : A*(u+ε+d.tau*t) ≤ η*c := by
    have hv := (le_div_iff₀ (mul_pos hA (by positivity : 0 < 2+d.tau))).mp hrA
    nlinarith [mul_le_mul_of_nonneg_left (by nlinarith [mul_lt_mul_of_pos_left htr hτ] :
      u+ε+d.tau*t ≤ (2+d.tau)*r) hA.le]
  have hH : c*(u+ε+d.tau*t) ≤ ‖currentD d ε t u*(2-currentD d ε t u)‖ := by
    rw [norm_mul]
    nlinarith [mul_le_mul_of_nonneg_left hf (norm_nonneg (currentD d ε t u))]
  have he : 1-(currentW d ε t u)^2 = currentD d ε t u*(2-currentD d ε t u) := by
    dsimp [currentD]; ring
  rw [he]
  have hL : 0 ≤ u+ε+d.tau*t := by positivity
  have habs := mul_le_mul_of_nonneg_right hAL hL
  have hηH := mul_le_mul_of_nonneg_left hH hη.le
  dsimp [A] at hAL habs
  nlinarith

theorem current_positive_cone (d : LocalBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε t u : ℝ,
      0 < ε → ε < r → 0 ≤ t → t < r → 0 ≤ u → u < r →
      (2/3:ℝ)*‖deriv (currentPhase d ε t) u‖ ≤ (deriv (currentPhase d ε t) u).re := by
  obtain ⟨r₁,hr₁,hmargin⟩ := current_positive_factor_margin d (1/50) (by norm_num)
  obtain ⟨r₂,hr₂,hbranch⟩ := current_branch_inclusion d
  have ha := d.a_pos
  have hd : ContinuousAt (fun z : ℝ × ℝ × ℝ => ‖currentDu d z.1 z.2.1 z.2.2-(d.a:ℂ)‖) 0 :=
    ((currentDu_continuous d).sub continuous_const).norm.continuousAt
  have he := hd.eventually_lt (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ × ℝ => d.a/100) 0)
    (by change ‖currentDu d 0 0 0-(d.a:ℂ)‖ < d.a/100; rw [currentDu_zero,sub_self,norm_zero]; positivity)
  obtain ⟨r₃,hr₃,hDu⟩ := Metric.eventually_nhds_iff.mp he
  let r := min r₁ (min r₂ r₃)
  refine ⟨r,lt_min hr₁ (lt_min hr₂ hr₃),?_⟩
  intro ε t u hε hεr ht htr hu hur
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrr₂ : r ≤ r₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hrr₃ : r ≤ r₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hm := hmargin ε t u hε (hεr.trans_le hrr₁) ht (htr.trans_le hrr₁) hu (hur.trans_le hrr₁)
  obtain ⟨hre,him⟩ := hbranch ε t u hε (hεr.trans_le hrr₂) ht (htr.trans_le hrr₂)
    (by simpa [abs_of_nonneg hu] using hur.trans_le hrr₂)
  have hz : dist (ε,t,u) (0:ℝ × ℝ × ℝ) < r₃ := by
    simpa [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,abs_of_pos hε,abs_of_nonneg ht,abs_of_nonneg hu]
      using And.intro (hεr.trans_le hrr₃) (And.intro (htr.trans_le hrr₃) (hur.trans_le hrr₃))
  have hhi : (1-(currentW d ε t u)^2).im < 0 := by
    simp [pow_two,Complex.mul_im]
    nlinarith [mul_pos hre him]
  have hs : Complex.sqrt (1-(currentW d ε t u)^2) ≠ 0 := by
    intro h
    have hv := sqrt_sq (1-(currentW d ε t u)^2)
    rw [h,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hv
    have hi := congrArg Complex.im hv
    simp only [Complex.zero_im] at hi
    linarith
  rw [currentPhase_deriv d ε t u hre him]
  exact quotient_two_thirds_cone _ _ d.a ha hs (sqrt_cone_of_real_margin _ hhi hm) (hDu hz).le

end
end IsingBulk.Branch


