import IsingBulk.Joint.Negative.FamilyRootBounds
import IsingBulk.Anisotropic.NegativeNormalForm.ScalarRootCenterControl

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Metric Filter IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_family_root_center_lipschitz (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {P : Set E} (hP : IsCompact P)
    (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta)) (hBn : ∀eta∈P,B (0,eta)≠0) :
    ∃r L : ℝ,0<r ∧ 0<L ∧ ∀eta∈P,∀d t : ℂ,‖d‖<r → ‖t‖<r →
      ‖Complex.sqrt (phaseEnergy (familyMember B eta) phi hphi d t 0)-1‖≤L*‖t-(1-Complex.cos d)‖ := by
  obtain ⟨a,L,ha,hL,_hsmall,hLip⟩ := compact_family_root_small B phi hphi hP hB hBn 1 zero_lt_one
  obtain ⟨c,hc,hbranch⟩ := compact_family_branch B phi hP hB hBn
  have htau : Tendsto (fun d : ℂ=>1-Complex.cos d) (𝓝 0) (𝓝 0) := by
    have hh : ContinuousAt (fun d : ℂ=>1-Complex.cos d) 0 := by fun_prop
    simpa using hh.tendsto
  obtain ⟨b,hb,hbs⟩ := Metric.eventually_nhds_iff.mp (htau.eventually (ball_mem_nhds (0:ℂ) ha))
  refine ⟨min a (min b c),L,lt_min ha (lt_min hb hc),hL,?_⟩
  intro eta heta d t hd ht
  have hda := hd.trans_le (min_le_left _ _)
  have hta := ht.trans_le (min_le_left _ _)
  have htau : ‖1-Complex.cos d‖<a := by
    simpa using hbs (show dist d 0<b by
      simpa using hd.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨hBa,hBn',hH⟩ := hbranch eta heta d
    (hd.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hp : ‖(t,(d,(0:ℂ)))‖<a := max_lt hta (max_lt hda (by simpa using ha))
  have hq : ‖(1-Complex.cos d,(d,(0:ℂ)))‖<a := max_lt htau (max_lt hda (by simpa using ha))
  have hh := hLip eta heta (t,(d,0)) (1-Complex.cos d,(d,0)) hp hq
  have hcenter : Complex.sqrt (phaseEnergy (familyMember B eta) phi hphi d (1-Complex.cos d) 0)=1 := by
    simpa using congrArg Complex.sqrt (phaseEnergy_center (familyMember B eta) phi hphi d hBa hBn' hH)
  rw [hcenter] at hh
  simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,max_self,
    max_eq_left (norm_nonneg _)] using hh

end
end IsingBulk.Joint.Negative
