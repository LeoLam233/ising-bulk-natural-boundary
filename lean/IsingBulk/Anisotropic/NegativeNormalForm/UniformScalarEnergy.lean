import IsingBulk.Anisotropic.NegativeNormalForm.UniformParameterQuotient
import IsingBulk.Anisotropic.NegativeNormalForm.JointFactorIdentification
import IsingBulk.Anisotropic.NegativeNormalForm.AnalyticSeparableMap
import IsingBulk.Anisotropic.NegativeNormalForm.HessianBounds

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology

 theorem phaseSecondFactor_eq_double_dslope_triple_eventually (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (hB : AnalyticAt ℂ B 0) :
    ∀ᶠ p : ScalarTriple in 𝓝 0,
      dslope (dslope (negativePhase B phi hphi p.1) p.2.1) p.2.1 (p.2.1+p.2.2)=
        phaseSecondFactor B phi hphi p.2.1 p.1 p.2.2 := by
  have ha : AnalyticAt ℂ (fun z : (ℂ × ℂ) × ℂ => (z.1.1,(z.1.2,z.2))) ((0,0),0) :=
    (analyticAt_fst.comp analyticAt_fst).prod
      ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)
  have hA := (phaseFirstFactor_triple_analyticAt B phi hphi hB).fun_comp_of_eq ha rfl
  have hH := (phaseSecondFactor_triple_analyticAt B phi hphi hB).fun_comp_of_eq ha rfl
  have he := ha.continuousAt.tendsto.eventually (phase_factors_triple_eventually B phi hphi hB)
  have hid := joint_double_dslope_eq_of_factorization
    (fun td : ℂ × ℂ => fun v => negativePhase B phi hphi td.1 (td.2+v))
    (fun z : (ℂ × ℂ) × ℂ => phaseFirstFactor B phi hphi z.1.2 z.1.1 z.2)
    (fun z : (ℂ × ℂ) × ℂ => phaseSecondFactor B phi hphi z.1.2 z.1.1 z.2)
    hA hH (by
      convert! he using 1
      simp only [phaseIncrement,add_zero])
  have hc : ContinuousAt (fun p : ScalarTriple => ((p.1,p.2.1),p.2.2)) 0 := by fun_prop
  simpa only [double_dslope_translate] using hc.tendsto.eventually hid

 theorem phaseEnergy_triple_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (hB : AnalyticAt ℂ B 0) (hBn : B 0 ≠ 0) :
    AnalyticAt ℂ (fun p : ScalarTriple => phaseEnergy B phi hphi p.2.1 p.1 p.2.2) 0 := by
  have ht : AnalyticAt ℂ (fun p : ScalarTriple => p.1) 0 := analyticAt_fst
  have hd : AnalyticAt ℂ (fun p : ScalarTriple => p.2.1) 0 := analyticAt_fst.comp analyticAt_snd
  have hc := (phaseParameterQuotient_joint_origin_analyticAt B phi hphi hB).fun_comp_of_eq
    (f := fun p : ScalarTriple => (p.1,p.2.1)) (ht.prod hd) rfl
  have hh := (centralHessian_analyticAt_zero B phi hB).comp (f := fun p : ScalarTriple => p.2.1) hd
  have hc0 : phaseParameterQuotient B phi hphi 0 0 ≠ 0 := by
    have hh := phaseParameterQuotient_center B phi hphi 0 (by simpa using hB)
    simp only [Complex.cos_zero,sub_self] at hh
    rw [hh]
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hphi) Complex.I_ne_zero)) hBn
  have hmodel : AnalyticAt ℂ (fun p : ScalarTriple =>
      -2/(centralHessian B phi p.2.1*phaseParameterQuotient B phi hphi p.2.1 p.1)*
      phaseSecondFactor B phi hphi p.2.1 p.1 p.2.2) 0 := (analyticAt_const.div (hh.mul hc)
    (by change centralHessian B phi 0 * phaseParameterQuotient B phi hphi 0 0 ≠ 0; simpa only [centralHessian_zero,one_mul] using hc0)).mul
      (phaseSecondFactor_triple_analyticAt B phi hphi hB)
  have hg : AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (0,0) := by
    simpa using negativePhase_analyticAt_center B phi hphi 0 (by simpa using hB)
  have he := (ht.prod hd).continuousAt.tendsto.eventually hg.eventually_analyticAt
  apply hmodel.congr
  filter_upwards [phaseSecondFactor_eq_double_dslope_triple_eventually B phi hphi hB,he] with p hp hgp
  have hgv : AnalyticAt ℂ (negativePhase B phi hphi p.1) p.2.1 :=
    hgp.comp (f := fun v : ℂ => (p.1,v)) (analyticAt_const.prod analyticAt_id)
  rw [phaseEnergy,energyQuotient_eq_double_dslope hgv,hp]

 theorem phaseRootEnergy_triple_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (hB : AnalyticAt ℂ B 0) (hBn : B 0 ≠ 0) :
    AnalyticAt ℂ (fun p : ScalarTriple => Complex.sqrt (phaseEnergy B phi hphi p.2.1 p.1 p.2.2)) 0 := by
  apply sqrt_analyticAt_one.comp_of_eq (phaseEnergy_triple_analyticAt B phi hphi hB hBn)
  simpa using phaseEnergy_center B phi hphi 0 (by simpa using hB) (by simpa using hBn)
    (by simp [centralHessian_zero])

end
end IsingBulk.Anisotropic.NegativeNormalForm
