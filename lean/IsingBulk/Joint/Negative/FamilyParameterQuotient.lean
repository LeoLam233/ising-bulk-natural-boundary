import IsingBulk.Joint.Negative.FamilyIdentities
import IsingBulk.Anisotropic.NegativeNormalForm.UniformParameterQuotient
import IsingBulk.Anisotropic.NegativeNormalForm.HessianBounds

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem family_parameterDivisor_analyticAt (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : (ℂ × ℂ) × E=>hyperbolicDivisor ((phi:ℂ)*Complex.I)
      (negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2-(phi:ℂ)*Complex.I)) ((0,0),eta) := by
  have hg0 : negativePhase (familyMember B eta) phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa using negativePhase_center (familyMember B eta) phi hphi 0
  have hg := familyPhase_analyticAt_center B phi hphi eta hB
  exact (hyperbolicDivisor_analyticAt ((phi:ℂ)*Complex.I)).fun_comp_of_eq
    (f:=fun q : (ℂ × ℂ) × E=>((phi:ℂ)*Complex.I,
      negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2-(phi:ℂ)*Complex.I))
    (analyticAt_const.prod (hg.sub analyticAt_const))
    (by simp [hg0])

theorem family_parameterFactor_analyticAt (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : (ℂ × ℂ) × E=>parameterFactor (familyMember B q.2) phi hphi q.1.1 q.1.2)
      ((0,0),eta) := by
  have hg0 : negativePhase (familyMember B eta) phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa using negativePhase_center (familyMember B eta) phi hphi 0
  have hbase : AnalyticAt ℂ (fun q : (ℂ × ℂ) × E=>(q.1.1,q.2)) ((0,0),eta) :=
    (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
  apply (hB.fun_comp_of_eq hbase rfl).div (family_parameterDivisor_analyticAt B phi hphi eta hB)
  simpa [hg0,Complex.sinh_mul_I,←Complex.ofReal_sin] using
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hphi) Complex.I_ne_zero

theorem family_parameterQuotient_eq_factor_eventually (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta)) :
    ∀ᶠq : (ℂ × ℂ) × E in 𝓝 ((0,0),eta),
      phaseParameterQuotient (familyMember B q.2) phi hphi q.1.2 q.1.1=
        parameterFactor (familyMember B q.2) phi hphi q.1.1 q.1.2 := by
  have hg0 : negativePhase (familyMember B eta) phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa using negativePhase_center (familyMember B eta) phi hphi 0
  have hden : ∀ᶠq : (ℂ × ℂ) × E in 𝓝 ((0,0),eta),
      hyperbolicDivisor ((phi:ℂ)*Complex.I)
        (negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2-(phi:ℂ)*Complex.I)≠0 :=
    (family_parameterDivisor_analyticAt B phi hphi eta hB).continuousAt.eventually_ne
    (by simpa [hg0,Complex.sinh_mul_I,←Complex.ofReal_sin] using
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hphi) Complex.I_ne_zero)
  have hWa : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × E=>negativeDispersion (familyMember B q.2) (Real.cos phi) q.1.1 q.1.2) ((0,0),eta) := by
    have ht : AnalyticAt ℂ (fun q : (ℂ × ℂ) × E=>q.1.1) ((0,0),eta) := analyticAt_fst.comp analyticAt_fst
    have hd : AnalyticAt ℂ (fun q : (ℂ × ℂ) × E=>q.1.2) ((0,0),eta) := analyticAt_snd.comp analyticAt_fst
    exact analyticAt_const.add ((hB.comp (f:=fun q : (ℂ × ℂ) × E=>(q.1.1,q.2)) (ht.prod analyticAt_snd)).mul
      ((ht.sub analyticAt_const).add (Complex.analyticAt_cos.comp hd)))
  have hcosh : ∀ᶠq : (ℂ × ℂ) × E in 𝓝 ((0,0),eta),
      Complex.cosh (negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2)=
        negativeDispersion (familyMember B q.2) (Real.cos phi) q.1.1 q.1.2 := by
    have hc := hWa.continuousAt.tendsto
    have hW0 : negativeDispersion (familyMember B eta) (Real.cos phi) 0 0=(Real.cos phi:ℂ) := by
      simp [negativeDispersion]
    rw [hW0] at hc
    exact hc.eventually (edgePhase_spec phi hphi).2.2.1
  have htau : Tendsto (fun q : (ℂ × ℂ) × E=>(1-Complex.cos q.1.2,q.2))
      (𝓝 ((0,0),eta)) (𝓝 (0,eta)) := by
    have hh : ContinuousAt (fun q : (ℂ × ℂ) × E=>(1-Complex.cos q.1.2,q.2)) ((0,0),eta) := by fun_prop
    simpa using hh.tendsto
  have hBe := htau.eventually hB.eventually_analyticAt
  filter_upwards [hden,hcosh,hBe] with q hp hc hb
  have hb' : AnalyticAt ℂ (familyMember B q.2) (1-Complex.cos q.1.2) :=
    hb.comp (f:=fun t : ℂ=>(t,q.2)) (analyticAt_id.prod analyticAt_const)
  by_cases he : q.1.1=1-Complex.cos q.1.2
  · rw [he,phaseParameterQuotient_center (familyMember B q.2) phi hphi q.1.2 hb']
    simp only [parameterFactor,negativePhase_center,sub_self,hyperbolicDivisor_zero,
      Complex.sinh_mul_I,←Complex.ofReal_sin,div_eq_mul_inv]
    ring
  · have hf := cosh_increment_factor ((phi:ℂ)*Complex.I)
      (negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2-(phi:ℂ)*Complex.I)
    simp only [add_sub_cancel] at hf
    rw [hc,Complex.cosh_mul_I,←Complex.ofReal_cos,
      phaseParameterQuotient_identity (familyMember B q.2) phi hphi q.1.2 q.1.1] at hf
    have hz : q.1.1-(1-Complex.cos q.1.2)≠0 := sub_ne_zero.mpr he
    apply (eq_div_iff hp).2
    have hzprod : (q.1.1-(1-Complex.cos q.1.2))*
        (phaseParameterQuotient (familyMember B q.2) phi hphi q.1.2 q.1.1 *
          hyperbolicDivisor ((phi:ℂ)*Complex.I)
            (negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2-(phi:ℂ)*Complex.I)-familyMember B q.2 q.1.1)=0 := by
      unfold negativeDispersion at hf
      rw [phaseParameterQuotient_identity (familyMember B q.2) phi hphi q.1.2 q.1.1]
      linear_combination -hf
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzprod).resolve_left hz)

theorem family_parameterQuotient_analyticAt (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : (ℂ × ℂ) × E=>phaseParameterQuotient (familyMember B q.2) phi hphi q.1.2 q.1.1)
      ((0,0),eta) := by
  apply (family_parameterFactor_analyticAt B phi hphi eta hB).congr
  filter_upwards [family_parameterQuotient_eq_factor_eventually B phi hphi eta hB] with q hq using hq.symm

theorem family_hessian_analyticAt (B : ℂ × E→ℂ) (phi : ℝ)
    (eta : E) (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : ℂ × E=>centralHessian (familyMember B q.2) phi q.1) (0,eta) := by
  have hd : AnalyticAt ℂ (fun q : ℂ × E=>q.1) (0,eta) := analyticAt_fst
  have hC := hB.comp_of_eq
    (f:=fun q : ℂ × E=>(1-Complex.cos q.1,q.2))
    ((analyticAt_const.sub (Complex.analyticAt_cos.comp hd)).prod analyticAt_snd) (by simp)
  exact (Complex.analyticAt_cos.comp hd).sub
    (((hC.mul analyticAt_const).div_const).mul ((Complex.analyticAt_sin.comp hd).pow 2))

end
end IsingBulk.Joint.Negative
