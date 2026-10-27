import IsingBulk.Preferred22.Transport
import IsingBulk.Preferred22.ComplexKernelBridge

namespace IsingBulk.Preferred22
noncomputable section
open scoped Topology BigOperators

/-- The actual moving inverse and phase obey the dispersion before taking
any limit, on the explicit inverse's cosine domain. -/
theorem preferredRegular_dispersion (s q : ℂ)
    (hc : Complex.cos ((q+preferredMovingBranch s)/2) ≠ 0) :
    Complex.cos (preferredMovingInverse s q)+Complex.cos (preferredRegularPhase s q)=temperatureTrace s := by
  have hh := complexRightInverse_dispersion (temperatureTrace s) (q+preferredMovingBranch s) hc
  convert! hh using 1
  congr 1
  unfold preferredRegularPhase preferredMovingInverse traceMovingInverse preferredMovingBranch
  congr 1
  ring

/-- The cancellation driving the regular one-body factor is a derivative
of the literal dispersion. It includes q=0 and does not divide by sin phi. -/
theorem preferredRegular_inverse_derivative_identity (s q : ℂ)
    (hc : Complex.cos ((q+preferredMovingBranch s)/2) ≠ 0)
    (hU : DifferentiableAt ℂ (preferredMovingInverse s) q) :
    preferredSourceUQ s q *
      (Complex.sin (preferredRegularPhase s q)-Complex.sin (preferredMovingInverse s q)) =
      Complex.sin (preferredRegularPhase s q) := by
  have hφ := ((hasDerivAt_id q).sub hU.hasDerivAt).add_const (preferredMovingBranch s)
  have hd := hU.hasDerivAt.ccos.add hφ.ccos
  have hne : ∀ᶠ v in 𝓝 q, Complex.cos ((v+preferredMovingBranch s)/2) ≠ 0 :=
    (by fun_prop : ContinuousAt (fun v : ℂ => Complex.cos ((v+preferredMovingBranch s)/2)) q).eventually_ne hc
  have heq : (fun v => Complex.cos (preferredMovingInverse s v)+
      Complex.cos (preferredRegularPhase s v)) =ᶠ[𝓝 q] (fun _ => temperatureTrace s) := by
    filter_upwards [hne] with v hv
    exact preferredRegular_dispersion s v hv
  have he := (hd.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const q (temperatureTrace s))
  change -Complex.sin (preferredMovingInverse s q)*preferredSourceUQ s q+
    -Complex.sin (preferredRegularPhase s q)*(1-preferredSourceUQ s q)=0 at he
  linear_combination he

/-- The analytic one-body extension obtained from the actual dispersion,
with the branch zero cancelled explicitly. -/
def preferredOneBodyExtension (s q : ℂ) : ℂ :=
  (Complex.I*(Complex.sin (preferredRegularPhase s q)-Complex.sin (preferredMovingInverse s q)))⁻¹

theorem preferredRegularOneBody_eq_extension (s q : ℂ)
    (hc : Complex.cos ((q+preferredMovingBranch s)/2) ≠ 0)
    (hU : DifferentiableAt ℂ (preferredMovingInverse s) q)
    (hs : Complex.sin (preferredRegularPhase s q) ≠ 0) :
    preferredRegularOneBody s q=preferredOneBodyExtension s q := by
  have hid := preferredRegular_inverse_derivative_identity s q hc hU
  have hg : Complex.sin (preferredRegularPhase s q)-Complex.sin (preferredMovingInverse s q) ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hid
    exact hs hid.symm
  have hu : preferredSourceUQ s q =
      Complex.sin (preferredRegularPhase s q)/
        (Complex.sin (preferredRegularPhase s q)-Complex.sin (preferredMovingInverse s q)) :=
    (eq_div_iff hg).mpr hid
  unfold preferredRegularOneBody preferredOneBodyExtension
  rw [hu,show Complex.I*preferredRegularPhase s q=preferredRegularPhase s q*Complex.I by ring,
    Complex.sinh_mul_I]
  field_simp

theorem preferredRegularPhase_reference (d : PreferredBranchData) :
    preferredRegularPhase (preferredSelectedPoint d) 0=0 := by
  unfold preferredRegularPhase
  rw [(preferredMovingInverse_center_germ d).self_of_nhds.1]
  ring

theorem preferredMovingBranch_reference (d : PreferredBranchData) :
    preferredMovingBranch (preferredSelectedPoint d)=-(d.b:ℂ) := by
  unfold preferredMovingBranch
  rw [temperatureTrace_preferredSelectedPoint,traceMovingBranch_reference]

theorem preferredMovingBranch_analyticAt_reference (d : PreferredBranchData) :
    AnalyticAt ℂ preferredMovingBranch (preferredSelectedPoint d) := by
  have hS : AnalyticAt ℂ temperatureTrace (preferredSelectedPoint d) :=
    analyticAt_id.add (analyticAt_id.inv (preferredSelectedPoint_ne_zero d))
  exact (traceMovingBranch_analyticAt_reference d).comp_of_eq hS
    (temperatureTrace_preferredSelectedPoint d)

theorem preferredRegularPhase_analyticAt_reference (d : PreferredBranchData) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredRegularPhase z.1 z.2) (preferredSelectedPoint d,0) := by
  have hB := AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := preferredMovingBranch)
    (preferredMovingBranch_analyticAt_reference d) (analyticAt_fst (p := (preferredSelectedPoint d,(0:ℂ))))
  exact (analyticAt_snd.sub (preferredMovingInverse_analyticAt_reference d)).add hB

/-- The source one-body factor is analytic through the moving branch point. -/
theorem preferredOneBodyExtension_analyticAt_reference (d : PreferredBranchData) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2) (preferredSelectedPoint d,0) := by
  have hU := preferredMovingInverse_analyticAt_reference d
  have hφ := preferredRegularPhase_analyticAt_reference d
  apply (analyticAt_const.mul ((Complex.analyticAt_sin.comp hφ).sub
    (Complex.analyticAt_sin.comp hU))).inv
  apply mul_ne_zero Complex.I_ne_zero
  change Complex.sin (preferredRegularPhase (preferredSelectedPoint d) 0)-
    Complex.sin (preferredMovingInverse (preferredSelectedPoint d) 0) ≠ 0
  rw [preferredRegularPhase_reference,Complex.sin_zero,
    (preferredMovingInverse_center_germ d).self_of_nhds.1,preferredMovingBranch_reference,
    Complex.sin_neg,zero_sub,neg_neg,← Complex.ofReal_sin]
  exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi d.b_pos d.b_lt).ne'

/-- Dispersion difference supplies the alternate pair quotient which removes
the double lower-branch denominator. -/
theorem preferred_half_kernel_branch_identity (S w₁ w₂ φ₁ φ₂ : ℂ)
    (h₁ : Complex.cos w₁+Complex.cos φ₁=S)
    (h₂ : Complex.cos w₂+Complex.cos φ₂=S)
    (hφ : Complex.sin ((φ₁+φ₂)/2) ≠ 0)
    (hw : Complex.sin ((w₁+w₂)/2) ≠ 0) :
    Complex.sin ((w₁-w₂)/2)/Complex.sinh (Complex.I*(φ₁+φ₂)/2) =
      Complex.I*Complex.sin ((φ₁-φ₂)/2)/Complex.sin ((w₁+w₂)/2) := by
  have hd : Complex.cos w₁-Complex.cos w₂=-(Complex.cos φ₁-Complex.cos φ₂) := by
    linear_combination h₁-h₂
  rw [Complex.cos_sub_cos,Complex.cos_sub_cos] at hd
  have hp : Complex.sin ((w₁+w₂)/2)*Complex.sin ((w₁-w₂)/2)+
      Complex.sin ((φ₁+φ₂)/2)*Complex.sin ((φ₁-φ₂)/2)=0 := by
    linear_combination (-1/2:ℂ)*hd
  rw [show Complex.I*(φ₁+φ₂)/2=((φ₁+φ₂)/2)*Complex.I by ring,Complex.sinh_mul_I]
  apply (div_eq_div_iff (mul_ne_zero hφ Complex.I_ne_zero) hw).mpr
  calc
    _ = -(Complex.sin ((φ₁+φ₂)/2)*Complex.sin ((φ₁-φ₂)/2)) := by linear_combination hp
    _ = _ := by ring_nf; simp [Complex.I_sq]

/-- Branch-regular extension of the literal half-angle kernel. -/
def preferredKernelBranchExtension (s q r : ℂ) : ℂ :=
  Complex.I*Complex.sin ((preferredRegularPhase s q-preferredRegularPhase s r)/2) /
    Complex.sin ((preferredMovingInverse s q+preferredMovingInverse s r)/2)

theorem preferredKernelBranchExtension_diagonal (s q : ℂ) : preferredKernelBranchExtension s q q=0 := by
  simp [preferredKernelBranchExtension]

theorem preferredRegularKernel_eq_branch_extension {N : ℕ} (s : ℂ) (q : Fin N → ℂ) (i j : Fin N)
    (hci : Complex.cos ((q i+preferredMovingBranch s)/2) ≠ 0)
    (hcj : Complex.cos ((q j+preferredMovingBranch s)/2) ≠ 0)
    (hφ : Complex.sin ((preferredRegularPhase s (q i)+preferredRegularPhase s (q j))/2) ≠ 0)
    (hw : Complex.sin ((preferredMovingInverse s (q i)+preferredMovingInverse s (q j))/2) ≠ 0) :
    preferredRegularKernel s q i j=preferredKernelBranchExtension s (q i) (q j) :=
  preferred_half_kernel_branch_identity _ _ _ _ _ (preferredRegular_dispersion s (q i) hci)
    (preferredRegular_dispersion s (q j) hcj) hφ hw

/-- Joint analyticity of the actual pair-kernel extension through the double
lower branch. This conclusion is proved from its source formula. -/
theorem preferredKernelBranchExtension_analyticAt_reference (d : PreferredBranchData) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => preferredKernelBranchExtension z.1 z.2.1 z.2.2)
      (preferredSelectedPoint d,0,0) := by
  let x : ℂ × ℂ × ℂ := (preferredSelectedPoint d,0,0)
  have hp : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.1)) x :=
    analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have hq : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => (z.1,z.2.2)) x :=
    analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hU₁ := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1))
    (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (preferredMovingInverse_analyticAt_reference d) hp
  have hU₂ := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2))
    (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (preferredMovingInverse_analyticAt_reference d) hq
  have hφ₁ := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.1))
    (g := fun z : ℂ × ℂ => preferredRegularPhase z.1 z.2) (preferredRegularPhase_analyticAt_reference d) hp
  have hφ₂ := AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => (z.1,z.2.2))
    (g := fun z : ℂ × ℂ => preferredRegularPhase z.1 z.2) (preferredRegularPhase_analyticAt_reference d) hq
  apply (analyticAt_const.mul (Complex.analyticAt_sin.comp
    ((hφ₁.sub hφ₂).div_const (c := (2:ℂ))))).div
    (Complex.analyticAt_sin.comp ((hU₁.add hU₂).div_const (c := (2:ℂ))))
  change Complex.sin ((preferredMovingInverse (preferredSelectedPoint d) 0+
    preferredMovingInverse (preferredSelectedPoint d) 0)/2) ≠ 0
  rw [(preferredMovingInverse_center_germ d).self_of_nhds.1,preferredMovingBranch_reference]
  rw [show (-(d.b:ℂ)+ -(d.b:ℂ))/2=-(d.b:ℂ) by ring,Complex.sin_neg]
  exact neg_ne_zero.mpr (by exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi d.b_pos d.b_lt).ne')

/-- The genuine analytic branch extension has a uniform diagonal zero
bound in the regular coordinate, including the simultaneous branch point. -/
theorem preferredKernelBranchExtension_local_bound (d : PreferredBranchData) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ s q z : ℂ,
      ‖s-preferredSelectedPoint d‖ < r → ‖q‖ < r → ‖z‖ < r →
      ‖preferredKernelBranchExtension s q z‖ ≤ C*‖q-z‖ := by
  obtain ⟨K,U,hU,hLip⟩ := (preferredKernelBranchExtension_analyticAt_reference d).hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨(K:ℝ)+1,r,by positivity,hr,?_⟩
  intro s q z hs hq hz
  have hx : (s,q,z) ∈ U := hball (by
    simpa only [Metric.mem_ball,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
      sub_zero,max_lt_iff] using And.intro hs (And.intro hq hz))
  have hdiag : (s,q,q) ∈ U := hball (by
    simpa only [Metric.mem_ball,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
      sub_zero,max_lt_iff] using And.intro hs (And.intro hq hq))
  have hh := hLip.dist_le_mul (s,q,z) hx (s,q,q) hdiag
  rw [preferredKernelBranchExtension_diagonal,dist_zero_right] at hh
  have hd : dist (s,q,z) (s,q,q)=‖q-z‖ := by
    rw [dist_eq_norm]
    simp [Prod.norm_def,norm_sub_rev]
  rw [hd] at hh
  exact hh.trans (by nlinarith [norm_nonneg (q-z)])

/-- All mixed jets of the actual regular one-body extension are bounded on
one fixed branch neighborhood. The radius is chosen before the jet order. -/
theorem preferredOneBodyExtension_local_jets (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ z ∈ Metric.closedBall (preferredSelectedPoint d,(0:ℂ)) r,
      ‖iteratedFDeriv ℂ j (fun x : ℂ × ℂ => preferredOneBodyExtension x.1 x.2) z‖ ≤ C := by
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp
    (preferredOneBodyExtension_analyticAt_reference d).eventually_analyticAt
  refine ⟨r/2,half_pos hr,?_⟩
  intro j
  let K := Metric.closedBall (preferredSelectedPoint d,(0:ℂ)) (r/2)
  have ha : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => preferredOneBodyExtension x.1 x.2) K := by
    intro z hz
    exact hball (lt_of_le_of_lt hz (by linarith))
  have hc : ContinuousOn (iteratedFDeriv ℂ j
      (fun x : ℂ × ℂ => preferredOneBodyExtension x.1 x.2)) K := by
    intro z hz
    exact ((ha.iteratedFDeriv j) z hz).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := (isCompact_closedBall (preferredSelectedPoint d,(0:ℂ)) (r/2)).exists_bound_of_continuousOn hc
  refine ⟨max C 0+1,by positivity,?_⟩
  intro z hz
  exact (hC z hz).trans (by have := le_max_left C 0; linarith)

/-- All mixed jets of the actual regular pair extension are bounded on
one fixed branch neighborhood, uniformly before taking radial limits. -/
theorem preferredKernelBranchExtension_local_jets (d : PreferredBranchData) :
    ∃ r : ℝ, 0 < r ∧ ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ z ∈ Metric.closedBall (preferredSelectedPoint d,(0:ℂ),(0:ℂ)) r,
      ‖iteratedFDeriv ℂ j (fun x : ℂ × ℂ × ℂ => preferredKernelBranchExtension x.1 x.2.1 x.2.2) z‖ ≤ C := by
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp
    (preferredKernelBranchExtension_analyticAt_reference d).eventually_analyticAt
  refine ⟨r/2,half_pos hr,?_⟩
  intro j
  let K := Metric.closedBall (preferredSelectedPoint d,(0:ℂ),(0:ℂ)) (r/2)
  have ha : AnalyticOnNhd ℂ
      (fun x : ℂ × ℂ × ℂ => preferredKernelBranchExtension x.1 x.2.1 x.2.2) K := by
    intro z hz
    exact hball (lt_of_le_of_lt hz (by linarith))
  have hc : ContinuousOn (iteratedFDeriv ℂ j
      (fun x : ℂ × ℂ × ℂ => preferredKernelBranchExtension x.1 x.2.1 x.2.2)) K := by
    intro z hz
    exact ((ha.iteratedFDeriv j) z hz).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := (isCompact_closedBall (preferredSelectedPoint d,(0:ℂ),(0:ℂ)) (r/2)).exists_bound_of_continuousOn hc
  refine ⟨max C 0+1,by positivity,?_⟩
  intro z hz
  exact (hC z hz).trans (by have := le_max_left C 0; linarith)

/-- One quotient patches both exact dispersion identities. Its denominator
stays positive on the entire real regular inverse product, including the
double branch, rather than merely on a branch subchart. -/
def preferredKernelExtension (s q r : ℂ) : ℂ :=
  let w₁ := preferredMovingInverse s q
  let w₂ := preferredMovingInverse s r
  let φ₁ := preferredRegularPhase s q
  let φ₂ := preferredRegularPhase s r
  (-Complex.I*Complex.sin ((w₁-w₂)/2)*Complex.sin ((φ₁+φ₂)/2)+
    Complex.I*Complex.sin ((φ₁-φ₂)/2)*Complex.sin ((w₁+w₂)/2)) /
    ((Complex.sin ((φ₁+φ₂)/2))^2+(Complex.sin ((w₁+w₂)/2))^2)

theorem preferredKernelExtension_diagonal (s q : ℂ) : preferredKernelExtension s q q=0 := by
  simp [preferredKernelExtension]

theorem preferred_half_kernel_extension_identity (S w₁ w₂ φ₁ φ₂ : ℂ)
    (h₁ : Complex.cos w₁+Complex.cos φ₁=S)
    (h₂ : Complex.cos w₂+Complex.cos φ₂=S)
    (hφ : Complex.sin ((φ₁+φ₂)/2) ≠ 0)
    (hD : (Complex.sin ((φ₁+φ₂)/2))^2+(Complex.sin ((w₁+w₂)/2))^2 ≠ 0) :
    Complex.sin ((w₁-w₂)/2)/Complex.sinh (Complex.I*(φ₁+φ₂)/2) =
      (-Complex.I*Complex.sin ((w₁-w₂)/2)*Complex.sin ((φ₁+φ₂)/2)+
        Complex.I*Complex.sin ((φ₁-φ₂)/2)*Complex.sin ((w₁+w₂)/2)) /
        ((Complex.sin ((φ₁+φ₂)/2))^2+(Complex.sin ((w₁+w₂)/2))^2) := by
  have hp : Complex.sin ((w₁+w₂)/2)*Complex.sin ((w₁-w₂)/2)+
      Complex.sin ((φ₁+φ₂)/2)*Complex.sin ((φ₁-φ₂)/2)=0 := by
    have hd : Complex.cos w₁-Complex.cos w₂=-(Complex.cos φ₁-Complex.cos φ₂) := by
      linear_combination h₁-h₂
    rw [Complex.cos_sub_cos,Complex.cos_sub_cos] at hd
    linear_combination (-1/2:ℂ)*hd
  rw [show Complex.I*(φ₁+φ₂)/2=((φ₁+φ₂)/2)*Complex.I by ring,Complex.sinh_mul_I]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring_nf at hp
  linear_combination Complex.sin (w₁*(1/2)+w₂*(1/2))*hp

/-- The patched denominator is strictly positive for any two real inverse
half-differences in (0,pi/2); this includes all the manuscript's right interval. -/
theorem preferred_real_kernel_denominator_pos (x y a b : ℝ)
    (ha : 0<a) (hb : 0<b) (ha' : a<Real.pi/2) (hb' : b<Real.pi/2) :
    0 < (Real.sin ((x+y+a+b)/2))^2+(Real.sin ((x+y-a-b)/2))^2 := by
  let X := (x+y)/2
  let A := (a+b)/2
  have hs : (Real.sin ((x+y+a+b)/2))^2+(Real.sin ((x+y-a-b)/2))^2 =
      1-Real.cos (x+y)*Real.cos (a+b) := by
    have hx := Real.sin_sq_add_cos_sq X
    have hy := Real.sin_sq_add_cos_sq A
    have hxy := congrArg (fun t : ℝ => t*(Real.cos A)^2) hx
    have hyx := congrArg (fun t : ℝ => t*(Real.cos X)^2) hy
    rw [show (x+y+a+b)/2=X+A by dsimp [X,A]; ring,
      show (x+y-a-b)/2=X-A by dsimp [X,A]; ring,
      show x+y=2*X by dsimp [X]; ring,
      show a+b=2*A by dsimp [A]; ring,
      Real.sin_add,Real.sin_sub,Real.cos_two_mul,Real.cos_two_mul]
    nlinarith
  rw [hs]
  have hsum : 0<a+b := add_pos ha hb
  have hsumpi : a+b<Real.pi := by linarith
  have hl : -1<Real.cos (a+b) := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi hsum.le (le_refl Real.pi) hsumpi
    simpa using hh
  have hu : Real.cos (a+b)<1 := by
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0) hsumpi.le hsum
    simpa using hh
  have hp : |Real.cos (x+y)*Real.cos (a+b)|<1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans_lt
      (by simpa using (abs_lt.mpr ⟨hl,hu⟩))
  linarith [le_abs_self (Real.cos (x+y)*Real.cos (a+b))]

end
end IsingBulk.Preferred22
