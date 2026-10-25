import IsingBulk.Joint.Negative.FamilyHadamard
import IsingBulk.Joint.Negative.FamilyEnergy
import IsingBulk.Anisotropic.NegativeNormalForm.ScalarQuadraticControl

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1000000

theorem compact_family_even_quadratic (S : ScalarTriple × E→ℂ)
    {P : Set E} (hP : IsCompact P) (hS : ∀eta∈P,AnalyticAt ℂ S (0,eta))
    (heven : ∀eta∈P,∀t v : ℂ,S ((t,(0,-v)),eta)=S ((t,(0,v)),eta)) :
    ∃r L : ℝ,0<r ∧ 0<L ∧ ∀eta∈P,∀p : ScalarTriple,‖p‖<r →
      ‖S (p,eta)-S ((p.1,(p.2.1,0)),eta)‖≤L*(‖p.2.1‖+‖p.2.2‖)*‖p.2.2‖ := by
  let g : ((ℂ × ℂ) × E) × ℂ→ℂ := fun z=>S ((z.1.1.1,(z.1.1.2,z.2)),z.1.2)
  have hg (eta : E) (heta : eta∈P) : AnalyticAt ℂ g (((0,0),eta),0) :=
    (hS eta heta).fun_comp_of_eq
      (((analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)).prod
        ((analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst)).prod analyticAt_snd)).prod
        (analyticAt_snd.comp analyticAt_fst)) rfl
  let Q : ScalarTriple × E→ℂ := fun q=>
    coordinateHadamard (fun z : (ℂ × ℂ) × ℂ=>S ((z.1.1,(z.1.2,z.2)),q.2))
      ((q.1.1,q.1.2.1),q.1.2.2)
  have hm (eta : E) : AnalyticAt ℂ (fun q : ScalarTriple × E=>(((q.1.1,q.1.2.1),q.1.2.2),q.2)) (0,eta) :=
    (((analyticAt_fst.comp analyticAt_fst).prod
      (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst))).prod
      (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst))).prod analyticAt_snd
  have hqa (eta : E) (heta : eta∈P) : AnalyticAt ℂ Q (0,eta) :=
    (family_coordinateHadamard_analyticAt g eta (hg eta heta)).fun_comp_of_eq (hm eta) rfl
  let G : Set (ScalarTriple × E) := {q |
    S q-S ((q.1.1,(q.1.2.1,0)),q.2)=q.1.2.2*Q q}
  obtain ⟨s,hs,hid⟩ := compact_product_tube (X:=ScalarTriple) hP
    (isOpen_interior : IsOpen (interior G)) (by
      intro eta heta
      apply mem_interior_iff_mem_nhds.mpr
      exact (hm eta).continuousAt.tendsto.eventually (family_coordinateHadamard_identity g eta (hg eta heta)))
  obtain ⟨r0,L,M,hr0,hL,_hM,_hbound,hLip⟩ := compact_analytic_uniform_lipschitz Q hP hqa
  obtain ⟨r1,M1,hr1,_hM1,hSa⟩ := compact_analytic_uniform_bound S hP hS
  let r := min r0 (min r1 s)
  have hr : 0<r := lt_min hr0 (lt_min hr1 hs)
  have hr0' : r≤r0 := min_le_left _ _
  have hr1' : r≤r1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrs : r≤s := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,L,hr,hL,?_⟩
  intro eta heta p hp
  have ht : ‖p.1‖<r1 := (norm_fst_le p).trans_lt (hp.trans_le hr1')
  have hbase : ‖(p.1,((0:ℂ),(0:ℂ)))‖<r0 := by
    simpa only [Prod.norm_def,norm_zero,max_self,max_eq_left (norm_nonneg _)] using
      (norm_fst_le p).trans_lt (hp.trans_le hr0')
  have hzero : Q ((p.1,(0,0)),eta)=0 := by
    change coordinateHadamard (fun z : (ℂ × ℂ) × ℂ=>S ((z.1.1,(z.1.2,z.2)),eta)) ((p.1,0),0)=0
    rw [coordinateHadamard_at_zero_last]
    have hlocal : AnalyticAt ℂ (fun z : (ℂ × ℂ) × ℂ=>S ((z.1.1,(z.1.2,z.2)),eta)) ((p.1,0),0) :=
      ((hSa eta heta (p.1,(0,0)) (by simpa using ht)).1).comp
        (f:=fun z : (ℂ × ℂ) × ℂ=>((z.1.1,(z.1.2,z.2)),eta))
        (((analyticAt_fst.comp analyticAt_fst).prod
          ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)).prod analyticAt_const)
    have hline : HasDerivAt (fun v : ℂ=>((p.1,(0:ℂ)),v)) ((0:ℂ × ℂ),1) 0 :=
      (hasDerivAt_const (0:ℂ) (p.1,(0:ℂ))).prodMk (hasDerivAt_id (0:ℂ))
    have hd := (hlocal.differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline).deriv
    exact hd.symm.trans (deriv_zero_of_even_complex _ (heven eta heta p.1))
  have heq : S (p,eta)-S ((p.1,(p.2.1,0)),eta)=p.2.2*Q (p,eta) :=
    interior_subset (s:=G) (hid eta heta p (hp.trans_le hrs))
  have hq := hLip eta heta p (p.1,(0,0)) (hp.trans_le hr0') hbase
  rw [hzero,sub_zero] at hq
  have hdist : ‖p-(p.1,(0,0))‖≤‖p.2.1‖+‖p.2.2‖ := by
    simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,sub_zero]
    exact max_le (by positivity) (max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _)))
  have hq' := hq.trans (mul_le_mul_of_nonneg_left hdist hL.le)
  rw [heq,norm_mul]
  exact (mul_le_mul_of_nonneg_left hq' (norm_nonneg _)).trans_eq (by ring)

theorem compact_family_root_quadratic (B : ℂ × E→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    {P : Set E} (hP : IsCompact P) (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈P,B (0,eta)≠0) :
    ∃r L : ℝ,0<r ∧ 0<L ∧ ∀eta∈P,∀p : ScalarTriple,‖p‖<r →
      ‖Complex.sqrt (phaseEnergy (familyMember B eta) phi hphi p.2.1 p.1 p.2.2)-
        Complex.sqrt (phaseEnergy (familyMember B eta) phi hphi p.2.1 p.1 0)‖≤
        L*(‖p.2.1‖+‖p.2.2‖)*‖p.2.2‖ :=
  compact_family_even_quadratic _ hP
    (fun eta heta=>family_rootEnergy_analyticAt B phi hphi eta (hB eta heta) (hBn eta heta))
    (fun eta _ t v=>congrArg Complex.sqrt (phaseEnergy_even_at_delta_zero (familyMember B eta) phi hphi t v))

end
end IsingBulk.Joint.Negative
