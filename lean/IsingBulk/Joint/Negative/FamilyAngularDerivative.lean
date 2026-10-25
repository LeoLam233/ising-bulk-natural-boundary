import IsingBulk.Joint.Negative.CompactAnalyticBounds
import IsingBulk.Anisotropic.NegativeNormalForm.ScalarEvenCancellation

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.First
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def angularFamilyJet (S : ScalarTriple × E→ℂ) (q : ScalarTriple × E) : ℂ :=
  jointParameterJet (fun z : ℂ × (ℂ × (ℂ × E))=>S ((z.2.1,(z.2.2.1,z.1)),z.2.2.2)) 1
    (q.1.2.2,(q.1.1,(q.1.2.1,q.2)))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem angularFamilyJet_eq (S : ScalarTriple × E→ℂ) (q : ScalarTriple × E) :
    angularFamilyJet S q=deriv (fun v=>S ((q.1.1,(q.1.2.1,v)),q.2)) q.1.2.2 := by
  rw [angularFamilyJet,jointParameterJet_eq]
  rfl

theorem angularFamilyJet_analyticAt (S : ScalarTriple × E→ℂ) (eta : E)
    (hS : AnalyticAt ℂ S (0,eta)) : AnalyticAt ℂ (angularFamilyJet S) (0,eta) := by
  have hF : AnalyticAt ℂ (fun z : ℂ × (ℂ × (ℂ × E))=>S ((z.2.1,(z.2.2.1,z.1)),z.2.2.2))
      (0,(0,(0,eta))) := (hS.fun_comp_of_eq
        (((analyticAt_fst.comp analyticAt_snd).prod
          ((analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)).prod analyticAt_fst)).prod
          (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd))) rfl)
  exact (jointParameterJet_analyticAt hF 1).fun_comp_of_eq
    ((analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)).prod
      ((analyticAt_fst.comp analyticAt_fst).prod
        ((analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)).prod analyticAt_snd))) rfl

theorem compact_family_angular_derivative (S : ScalarTriple × E→ℂ)
    {P : Set E} (hP : IsCompact P) (hS : ∀eta∈P,AnalyticAt ℂ S (0,eta))
    (heven : ∀eta∈P,∀t v : ℂ,S ((t,(0,-v)),eta)=S ((t,(0,v)),eta)) :
    ∃r L : ℝ,0<r ∧ 0<L ∧ ∀eta∈P,∀p : ScalarTriple,‖p‖<r →
      ‖deriv (fun v=>S ((p.1,(p.2.1,v)),eta)) p.2.2‖≤L*(‖p.2.1‖+‖p.2.2‖) := by
  obtain ⟨r,L,M,hr,hL,_hM,_ha,hl⟩ := compact_analytic_uniform_lipschitz (angularFamilyJet S) hP
    (fun eta heta=>angularFamilyJet_analyticAt S eta (hS eta heta))
  refine ⟨r,L,hr,hL,?_⟩
  intro eta heta p hp
  have hbase : ‖(p.1,((0:ℂ),(0:ℂ)))‖<r := by
    simpa only [Prod.norm_def,norm_zero,max_self,max_eq_left (norm_nonneg _)] using
      (norm_fst_le p).trans_lt hp
  have hzero : angularFamilyJet S ((p.1,(0,0)),eta)=0 := by
    rw [angularFamilyJet_eq]
    exact deriv_zero_of_even_complex _ (heven eta heta p.1)
  have hh := hl eta heta p (p.1,(0,0)) hp hbase
  rw [hzero,sub_zero,angularFamilyJet_eq] at hh
  have hd : ‖p-(p.1,(0,0))‖≤‖p.2.1‖+‖p.2.2‖ := by
    simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,sub_zero]
    exact max_le (by positivity) (max_le (le_add_of_nonneg_right (norm_nonneg _))
      (le_add_of_nonneg_left (norm_nonneg _)))
  exact hh.trans (mul_le_mul_of_nonneg_left hd hL.le)

end
end IsingBulk.Joint.Negative
