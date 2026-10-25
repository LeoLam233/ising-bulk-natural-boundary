import IsingBulk.Joint.Negative.FamilyParameterQuotient
import IsingBulk.Joint.Negative.FamilyDividedDifferences
import IsingBulk.Anisotropic.NegativeNormalForm.UniformScalarEnergy

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem family_secondFactor_eq_double_dslope (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta)) :
    ∀ᶠq : ScalarTriple × E in 𝓝 (0,eta),
      dslope (dslope (negativePhase (familyMember B q.2) phi hphi q.1.1) q.1.2.1)
        q.1.2.1 (q.1.2.1+q.1.2.2)=
      phaseSecondFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2 := by
  have ha : AnalyticAt ℂ (fun z : ((ℂ × ℂ) × E) × ℂ=>((z.1.1.1,(z.1.1.2,z.2)),z.1.2))
      (((0,0),eta),0) :=
    ((analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)).prod
      ((analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst)).prod analyticAt_snd)).prod
      (analyticAt_snd.comp analyticAt_fst)
  have hA := (family_phaseFirstFactor_analyticAt B phi hphi eta hB).fun_comp_of_eq ha rfl
  have hH := (family_phaseSecondFactor_analyticAt B phi hphi eta hB).fun_comp_of_eq ha rfl
  have he := ha.continuousAt.tendsto.eventually (family_factors_eventually B phi hphi eta hB)
  have hid := joint_double_dslope_eq_of_factorization_at
    (fun q : (ℂ × ℂ) × E=>fun v=>negativePhase (familyMember B q.2) phi hphi q.1.1 (q.1.2+v))
    (fun z : ((ℂ × ℂ) × E) × ℂ=>phaseFirstFactor (familyMember B z.1.2) phi hphi z.1.1.2 z.1.1.1 z.2)
    (fun z : ((ℂ × ℂ) × E) × ℂ=>phaseSecondFactor (familyMember B z.1.2) phi hphi z.1.1.2 z.1.1.1 z.2)
    ((0,0),eta) hA hH (by
      convert! he using 1
      simp only [phaseIncrement,add_zero])
  have hc : ContinuousAt (fun q : ScalarTriple × E=>(((q.1.1,q.1.2.1),q.2),q.1.2.2)) (0,eta) := by fun_prop
  simpa only [double_dslope_translate] using hc.tendsto.eventually hid

theorem family_energy_analyticAt (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta)) (hBn : B (0,eta)≠0) :
    AnalyticAt ℂ (fun q : ScalarTriple × E=>phaseEnergy (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2)
      (0,eta) := by
  have ht : AnalyticAt ℂ (fun q : ScalarTriple × E=>q.1.1) (0,eta) := analyticAt_fst.comp analyticAt_fst
  have hd : AnalyticAt ℂ (fun q : ScalarTriple × E=>q.1.2.1) (0,eta) := analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have he : AnalyticAt ℂ (fun q : ScalarTriple × E=>q.2) (0,eta) := analyticAt_snd
  have hc := (family_parameterQuotient_analyticAt B phi hphi eta hB).fun_comp_of_eq
    (f:=fun q : ScalarTriple × E=>((q.1.1,q.1.2.1),q.2)) ((ht.prod hd).prod he) rfl
  have hh := (family_hessian_analyticAt B phi eta hB).comp
    (f:=fun q : ScalarTriple × E=>(q.1.2.1,q.2)) (hd.prod he)
  have hc0 : phaseParameterQuotient (familyMember B eta) phi hphi 0 0≠0 := by
    have hc := phaseParameterQuotient_center (familyMember B eta) phi hphi 0
      (by simpa using familyMember_analyticAt hB)
    simp only [Complex.cos_zero,sub_self] at hc
    rw [hc]
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hphi) Complex.I_ne_zero)) hBn
  have hmodel : AnalyticAt ℂ (fun q : ScalarTriple × E=>
      -2/(centralHessian (familyMember B q.2) phi q.1.2.1 *
        phaseParameterQuotient (familyMember B q.2) phi hphi q.1.2.1 q.1.1)*
        phaseSecondFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2) (0,eta) :=
    (analyticAt_const.div (hh.mul hc) (by
      change centralHessian (familyMember B eta) phi 0*phaseParameterQuotient (familyMember B eta) phi hphi 0 0≠0
      simpa only [centralHessian_zero,one_mul] using hc0)).mul
      (family_phaseSecondFactor_analyticAt B phi hphi eta hB)
  have hg := familyPhase_analyticAt_center B phi hphi eta hB
  have hev := ((ht.prod hd).prod he).continuousAt.tendsto.eventually hg.eventually_analyticAt
  apply hmodel.congr
  filter_upwards [family_secondFactor_eq_double_dslope B phi hphi eta hB,hev] with q hq hgq
  have hgv : AnalyticAt ℂ (negativePhase (familyMember B q.2) phi hphi q.1.1) q.1.2.1 :=
    hgq.comp (f:=fun v : ℂ=>((q.1.1,v),q.2))
      ((analyticAt_const.prod analyticAt_id).prod analyticAt_const)
  rw [phaseEnergy,energyQuotient_eq_double_dslope hgv,hq]

theorem family_rootEnergy_analyticAt (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta)) (hBn : B (0,eta)≠0) :
    AnalyticAt ℂ (fun q : ScalarTriple × E=>Complex.sqrt
      (phaseEnergy (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2)) (0,eta) := by
  apply sqrt_analyticAt_one.comp_of_eq (family_energy_analyticAt B phi hphi eta hB hBn)
  change phaseEnergy (familyMember B eta) phi hphi 0 0 0=1
  simpa using phaseEnergy_center (familyMember B eta) phi hphi 0
    (by simpa using familyMember_analyticAt hB) (by simpa [familyMember] using hBn) (by simp [centralHessian_zero])

end
end IsingBulk.Joint.Negative
