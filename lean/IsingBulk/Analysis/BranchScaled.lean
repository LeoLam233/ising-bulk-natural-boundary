import IsingBulk.Analysis.BranchSecondDerivative

/-! The positive-side scaling epsilon=u*v. The divided dispersion extends
continuously to (u,v)=(0,0), without dividing by u at the limit. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology

def coshSlope (d : LocalBranchData) (z : ℂ) : ℂ :=
  dslope Complex.cosh (-(d.thetaB:ℂ)*Complex.I) (-(d.thetaB:ℂ)*Complex.I+z)

theorem coshSlope_continuous (d : LocalBranchData) : ContinuousAt (coshSlope d) 0 := by
  have h : ContinuousAt (dslope Complex.cosh (-(d.thetaB:ℂ)*Complex.I)) (-(d.thetaB:ℂ)*Complex.I) :=
    continuousAt_dslope_same.mpr (Complex.hasDerivAt_cosh _).differentiableAt
  exact ContinuousAt.comp (g := dslope Complex.cosh (-(d.thetaB:ℂ)*Complex.I))
    (f := fun z : ℂ => -(d.thetaB:ℂ)*Complex.I+z) (by simp) (by fun_prop)

theorem coshSlope_zero (d : LocalBranchData) : coshSlope d 0 = -Complex.I*(d.a:ℂ) := by
  simp only [coshSlope,add_zero,dslope_same,Complex.deriv_cosh,neg_mul,
    Complex.sinh_neg,Complex.sinh_mul_I,← Complex.ofReal_sin]
  dsimp [LocalBranchData.a]
  ring

theorem coshSlope_identity (d : LocalBranchData) (z : ℂ) :
    z*coshSlope d z = Complex.cosh (-(d.thetaB:ℂ)*Complex.I+z)-(Real.cos d.thetaB:ℂ) := by
  simpa [coshSlope,smul_eq_mul,Complex.cosh_mul_I,← Complex.ofReal_cos] using
    sub_smul_dslope Complex.cosh (-(d.thetaB:ℂ)*Complex.I) (-(d.thetaB:ℂ)*Complex.I+z)

def scaledOriginalD (d : LocalBranchData) (z : ℝ × ℝ) : ℂ :=
  (-(d.c₀:ℂ)*z.2+Complex.I)*coshSlope d ((z.1:ℂ)*(-(d.c₀:ℂ)*z.2+Complex.I))-
    2*Complex.I*(Real.sin d.theta:ℂ)*z.2-
    ((z.1*z.2^2/(1+z.1*z.2):ℝ):ℂ)*((Real.cos d.theta:ℂ)-Complex.I*(Real.sin d.theta:ℂ))

theorem scaledOriginalD_zero (d : LocalBranchData) : scaledOriginalD d 0 = (d.a:ℂ) := by
  simp [scaledOriginalD,coshSlope_zero,← mul_assoc]

theorem scaledOriginalD_continuous (d : LocalBranchData) : ContinuousAt (scaledOriginalD d) 0 := by
  have hs : ContinuousAt (fun z : ℝ × ℝ => coshSlope d ((z.1:ℂ)*(-(d.c₀:ℂ)*z.2+Complex.I))) 0 :=
    ContinuousAt.comp (g := coshSlope d) (f := fun z : ℝ × ℝ => (z.1:ℂ)*(-(d.c₀:ℂ)*z.2+Complex.I))
      (by simpa using coshSlope_continuous d) (by fun_prop)
  unfold scaledOriginalD
  fun_prop (disch := norm_num)

theorem scaledOriginalD_identity (d : LocalBranchData) (u v : ℝ) (h : 1+u*v ≠ 0) :
    originalD d (u*v) u = (u:ℂ)*scaledOriginalD d (u,v) := by
  have hc := coshSlope_identity d ((u:ℂ)*(-(d.c₀:ℂ)*v+Complex.I))
  have ha : (Real.cos d.thetaB:ℂ) = 2*(Real.cos d.theta:ℂ)-1 := by exact_mod_cast d.angle_relation
  rw [originalD,← branchDModel_eq d (u*v) 0 u h]
  unfold branchDModel radialTraceModel scaledOriginalD
  push_cast
  push_cast at ha
  have he : -(d.c₀:ℂ)*((u:ℂ)*v)+(d.tau:ℂ)*0/2+(-(d.thetaB:ℂ)+(u:ℂ))*Complex.I =
      -(d.thetaB:ℂ)*Complex.I+(u:ℂ)*(-(d.c₀:ℂ)*v+Complex.I) := by ring
  rw [he]
  rw [show Complex.cosh (-(d.thetaB:ℂ)*Complex.I+(u:ℂ)*(-(d.c₀:ℂ)*v+Complex.I)) =
    (u:ℂ)*(-(d.c₀:ℂ)*v+Complex.I)*coshSlope d ((u:ℂ)*(-(d.c₀:ℂ)*v+Complex.I))+
      (Real.cos d.thetaB:ℂ) by linear_combination -hc]
  push_cast
  rw [ha]
  ring

theorem sqrt_positive_real_mul (r : ℝ) (hr : 0 < r) (z : ℂ) :
    Complex.sqrt ((r:ℂ)*z) = (Real.sqrt r:ℂ)*Complex.sqrt z := by
  by_cases hz : z = 0
  · simp [hz]
  have hr' : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  rw [sqrt_eq_exp (mul_ne_zero hr' hz),Complex.log_ofReal_mul hr hz,add_div,Complex.exp_add,
    Complex.ofReal_log hr.le,
    ← sqrt_eq_exp hr',← sqrt_eq_exp hz]
  congr 1
  rw [Complex.sqrt,Real.sqrt_eq_rpow,Complex.ofReal_cpow hr.le]
  norm_num

def scaledH (d : LocalBranchData) (z : ℝ × ℝ) : ℂ :=
  scaledOriginalD d z*(2-originalD d (z.1*z.2) z.1)

theorem originalD_scaled_continuous (d : LocalBranchData) :
    ContinuousAt (fun z : ℝ × ℝ => originalD d (z.1*z.2) z.1) 0 := by
  have h : ContinuousAt (fun z : ℝ × ℝ × ℝ => 1-currentW d z.1 z.2.1 z.2.2) 0 :=
    (currentW_continuous d).const_sub 1
  have hc : ContinuousAt (fun z : ℝ × ℝ => (z.1*z.2,(0:ℝ),z.1)) 0 := by fun_prop
  have hp : (fun z : ℝ × ℝ => (z.1*z.2,(0:ℝ),z.1)) 0 = (0:ℝ × ℝ × ℝ) := by simp
  have ho : ContinuousAt (fun z : ℝ × ℝ × ℝ => 1-currentW d z.1 z.2.1 z.2.2)
      ((fun z : ℝ × ℝ => (z.1*z.2,(0:ℝ),z.1)) 0) := by rw [hp]; exact h
  exact ContinuousAt.comp (g := fun z : ℝ × ℝ × ℝ => 1-currentW d z.1 z.2.1 z.2.2)
    (f := fun z : ℝ × ℝ => (z.1*z.2,(0:ℝ),z.1)) (x := 0) ho hc

theorem scaledH_zero (d : LocalBranchData) : scaledH d 0 = (2*d.a:ℝ) := by
  simp [scaledH,scaledOriginalD_zero,originalD,currentD,currentW_zero]
  ring

theorem scaledH_continuous (d : LocalBranchData) : ContinuousAt (scaledH d) 0 := by
  have hd := originalD_scaled_continuous d
  exact (scaledOriginalD_continuous d).mul (hd.const_sub 2)

def scaledSecond (d : LocalBranchData) (z : ℝ × ℝ) : ℂ :=
  (z.1:ℂ)*currentDuu d (z.1*z.2) 0 z.1/Complex.sqrt (scaledH d z)-
    (currentDu d (z.1*z.2) 0 z.1)^2*(1-originalD d (z.1*z.2) z.1)/
      Complex.sqrt (scaledH d z)^3

theorem sqrt_scaledH_zero (d : LocalBranchData) :
    Complex.sqrt (scaledH d 0) = (Real.sqrt (2*d.a):ℂ) := by
  have ha := d.a_pos
  rw [scaledH_zero,Complex.sqrt,Real.sqrt_eq_rpow,Complex.ofReal_cpow (by positivity : 0 ≤ 2*d.a)]
  norm_num

theorem scaledSecond_zero (d : LocalBranchData) :
    scaledSecond d 0 = -((d.a^2/Real.sqrt (2*d.a)^3:ℝ):ℂ) := by
  simp [scaledSecond,sqrt_scaledH_zero,currentDu_zero,originalD,currentD,currentW_zero]

theorem scaledSecond_continuous (d : LocalBranchData) : ContinuousAt (scaledSecond d) 0 := by
  have ha := d.a_pos
  have hs : ContinuousAt (fun z => Complex.sqrt (scaledH d z)) 0 :=
    (Complex.continuousAt_sqrt (by left; rw [scaledH_zero]; simp; positivity)).comp
      (scaledH_continuous d)
  have hn : Complex.sqrt (scaledH d 0) ≠ 0 := by rw [sqrt_scaledH_zero]; exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < 2*d.a)).ne'
  have hD := originalD_scaled_continuous d
  unfold scaledSecond
  have hU : ContinuousAt (fun z : ℝ × ℝ => currentDu d (z.1*z.2) 0 z.1) 0 := by unfold currentDu; fun_prop
  have hUU : ContinuousAt (fun z : ℝ × ℝ => currentDuu d (z.1*z.2) 0 z.1) 0 := by unfold currentDuu; fun_prop
  fun_prop (disch := positivity)

theorem scaledSecond_negative_near (d : LocalBranchData) :
    ∃ k r : ℝ, 0 < k ∧ 0 < r ∧ ∀ u v : ℝ,
      |u| < r → |v| < r → (scaledSecond d (u,v)).re ≤ -k := by
  let k := d.a^2/(2*Real.sqrt (2*d.a)^3)
  have ha := d.a_pos
  have hk : 0 < k := by dsimp [k]; positivity
  have hc := Complex.continuous_re.continuousAt.comp (scaledSecond_continuous d)
  have hzero : (scaledSecond d 0).re = -2*k := by
    rw [scaledSecond_zero]
    simp only [Complex.neg_re,Complex.ofReal_re]
    dsimp [k]
    ring
  have he := hc.eventually_lt (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ => -k) 0)
    (by change (scaledSecond d 0).re < -k; rw [hzero]; linarith)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨k,r,hk,hr,?_⟩
  intro u v hu hv
  have hz : dist (u,v) (0:ℝ × ℝ) < r := by simpa [dist_zero_right,Prod.norm_def,Real.norm_eq_abs] using And.intro hu hv
  exact (hball hz).le

theorem scaledSecond_identity (d : LocalBranchData) (u v : ℝ) (hu : 0 < u)
    (hε : 1+u*v ≠ 0) (hre : 0 < (currentW d (u*v) 0 u).re)
    (him : 0 < (currentW d (u*v) 0 u).im) :
    ((u*Real.sqrt u:ℝ):ℂ)*deriv (deriv (currentPhase d (u*v) 0)) u =
      scaledSecond d (u,v) := by
  have hD := scaledOriginalD_identity d u v hε
  have hH : 1-(currentW d (u*v) 0 u)^2 = (u:ℂ)*scaledH d (u,v) := by
    have he : 1-(currentW d (u*v) 0 u)^2 = originalD d (u*v) u*(2-originalD d (u*v) u) := by
      dsimp [originalD,currentD]; ring
    rw [he,scaledH]
    rw [hD]
    ring
  have hroot : Complex.sqrt (1-(currentW d (u*v) 0 u)^2) =
      (Real.sqrt u:ℂ)*Complex.sqrt (scaledH d (u,v)) := by rw [hH,sqrt_positive_real_mul u hu]
  have hsU : (Real.sqrt u:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hu).ne'
  have hs : Complex.sqrt (scaledH d (u,v)) ≠ 0 := by
    have hn := current_phase_sin_ne_zero d (u*v) 0 u hre him
    rw [currentPhase,sin_lowerArccos,hroot] at hn
    exact (mul_ne_zero_iff.mp hn).2
  have hU2 : (Real.sqrt u:ℂ)^2 = (u:ℂ) := by exact_mod_cast Real.sq_sqrt hu.le
  rw [currentPhase_second_deriv d (u*v) 0 u hre him,hroot]
  unfold scaledSecond
  change ((u*Real.sqrt u:ℝ):ℂ)*
    (currentDuu d (u*v) 0 u/((Real.sqrt u:ℂ)*Complex.sqrt (scaledH d (u,v)))-
      (currentDu d (u*v) 0 u)^2*(1-originalD d (u*v) u)/
        ((Real.sqrt u:ℂ)*Complex.sqrt (scaledH d (u,v)))^3) = _
  push_cast
  rw [← hU2]
  field_simp

end
end IsingBulk.Branch

