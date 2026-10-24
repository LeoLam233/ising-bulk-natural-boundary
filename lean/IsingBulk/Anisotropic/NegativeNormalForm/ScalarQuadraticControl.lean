import IsingBulk.Anisotropic.NegativeNormalForm.ScalarEvenCancellation

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology
set_option maxHeartbeats 800000

theorem analytic_even_axis_quadratic_control (S : ScalarTriple → ℂ)
    (ha : AnalyticAt ℂ S 0) (heven : ∀ t v : ℂ, S (t,(0,-v))=S (t,(0,v))) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ p : ScalarTriple, ‖p‖<r →
      ‖S p-S (p.1,(p.2.1,0))‖≤L*(‖p.2.1‖+‖p.2.2‖)*‖p.2.2‖ := by
  let g : (ℂ × ℂ) × ℂ → ℂ := fun z => S (z.1.1,(z.1.2,z.2))
  have hg : AnalyticAt ℂ g 0 := ha.fun_comp_of_eq
    (f := fun z : (ℂ × ℂ) × ℂ => (z.1.1,(z.1.2,z.2)))
    ((analyticAt_fst.comp analyticAt_fst).prod
      ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)) rfl
  let q : ScalarTriple → ℂ := fun p => coordinateHadamard g ((p.1,p.2.1),p.2.2)
  have hm : AnalyticAt ℂ (fun p : ScalarTriple => ((p.1,p.2.1),p.2.2)) 0 :=
    (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)).prod
      (analyticAt_snd.comp analyticAt_snd)
  have hq : AnalyticAt ℂ q 0 := (coordinateHadamard_analyticAt hg).fun_comp_of_eq hm rfl
  have hid : ∀ᶠ p : ScalarTriple in 𝓝 0,
      S p-S (p.1,(p.2.1,0))=p.2.2*q p := by
    exact hm.continuousAt.tendsto.eventually (coordinateHadamard_identity hg)
  have hc : ContinuousAt (fun p : ScalarTriple => ((p.1,(0:ℂ)),(0:ℂ))) 0 := by fun_prop
  have hzero : ∀ᶠ p : ScalarTriple in 𝓝 0, q (p.1,(0,0))=0 := by
    filter_upwards [hc.tendsto.eventually hg.eventually_analyticAt] with p hp
    change coordinateHadamard g ((p.1,0),0)=0
    rw [coordinateHadamard_at_zero_last]
    have hline : HasDerivAt (fun v : ℂ => ((p.1,(0:ℂ)),v)) ((0:ℂ × ℂ),1) 0 :=
      (hasDerivAt_const (0:ℂ) (p.1,(0:ℂ))).prodMk (hasDerivAt_id (0:ℂ))
    have hh := hp.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline
    have hd : deriv (fun v => g ((p.1,0),v)) 0=
        fderiv ℂ g ((p.1,0),0) ((0:ℂ × ℂ),1) := hh.deriv
    exact hd.symm.trans (deriv_zero_of_even_complex _ (heven p.1))
  obtain ⟨r,L,M,hr,hL,_hM,_hbound,hLip⟩ := analytic_scalarTriple_uniform_lipschitz hq
  obtain ⟨s,hs,hsmall⟩ := Metric.eventually_nhds_iff.mp (hid.and hzero)
  refine ⟨min r s,L,lt_min hr hs,hL,?_⟩
  intro p hp
  have hpr : ‖p‖<r := hp.trans_le (min_le_left _ _)
  have hps : dist p 0<s := by simpa using hp.trans_le (min_le_right _ _)
  obtain ⟨he,hz⟩ := hsmall hps
  have hbase : ‖(p.1,((0:ℂ),(0:ℂ)))‖<r := by
    simpa only [Prod.norm_def,norm_zero,max_self,max_eq_left (norm_nonneg _)] using
      (norm_fst_le p).trans_lt hpr
  have hQ := hLip p (p.1,(0,0)) hpr hbase
  rw [hz,sub_zero] at hQ
  have hdist : ‖p-(p.1,(0,0))‖≤‖p.2.1‖+‖p.2.2‖ := by
    simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,sub_zero]
    exact max_le (by positivity) (max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _)))
  have hQ' := hQ.trans (mul_le_mul_of_nonneg_left hdist hL.le)
  rw [he,norm_mul]
  calc
    _ ≤ ‖p.2.2‖*(L*(‖p.2.1‖+‖p.2.2‖)) := mul_le_mul_of_nonneg_left hQ' (norm_nonneg _)
    _ = _ := by ring

theorem phaseRootEnergy_quadratic_control (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ p : ScalarTriple, ‖p‖<r →
      ‖Complex.sqrt (phaseEnergy B phi hphi p.2.1 p.1 p.2.2)-
        Complex.sqrt (phaseEnergy B phi hphi p.2.1 p.1 0)‖≤
        L*(‖p.2.1‖+‖p.2.2‖)*‖p.2.2‖ :=
  analytic_even_axis_quadratic_control _ (phaseRootEnergy_triple_analyticAt B phi hphi hB hBn)
    (fun t v => congrArg Complex.sqrt (phaseEnergy_even_at_delta_zero B phi hphi t v))

end
end IsingBulk.Anisotropic.NegativeNormalForm
