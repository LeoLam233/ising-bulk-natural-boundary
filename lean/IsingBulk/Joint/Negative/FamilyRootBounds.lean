import IsingBulk.Joint.Negative.FamilyEnergy
import IsingBulk.Joint.Negative.CompactAnalyticBounds
import IsingBulk.Anisotropic.NegativeNormalForm.UniformRootBounds

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_family_root_small (B : ℂ × E→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    {P : Set E} (hP : IsCompact P) (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈P,B (0,eta)≠0) (ε : ℝ) (hε : 0<ε) :
    ∃r L : ℝ,0<r ∧ 0<L ∧
      (∀eta∈P,∀q : ScalarTriple,‖q‖<r →
        AnalyticAt ℂ (fun x : ScalarTriple=>Complex.sqrt (phaseEnergy (familyMember B eta) phi hphi x.2.1 x.1 x.2.2)) q ∧
        ‖Complex.sqrt (phaseEnergy (familyMember B eta) phi hphi q.2.1 q.1 q.2.2)-1‖≤ε) ∧
      (∀eta∈P,∀q q' : ScalarTriple,‖q‖<r → ‖q'‖<r →
        ‖Complex.sqrt (phaseEnergy (familyMember B eta) phi hphi q.2.1 q.1 q.2.2)-
          Complex.sqrt (phaseEnergy (familyMember B eta) phi hphi q'.2.1 q'.1 q'.2.2)‖≤L*‖q-q'‖) := by
  obtain ⟨r,L,M,hr,hL,_hM,ha,hl⟩ := compact_analytic_uniform_lipschitz
    (fun q : ScalarTriple × E=>Complex.sqrt (phaseEnergy (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2))
    hP (fun eta heta=>family_rootEnergy_analyticAt B phi hphi eta (hB eta heta) (hBn eta heta))
  refine ⟨min r (ε/(L+1)),L,lt_min hr (div_pos hε (by linarith)),hL,?_,?_⟩
  · intro eta heta q hq
    have hq' := hq.trans_le (min_le_left _ _)
    refine ⟨(ha eta heta q hq').1.comp (f:=fun x : ScalarTriple=>(x,eta))
      (analyticAt_id.prod analyticAt_const),?_⟩
    have hh := hl eta heta q 0 hq' (by simpa using hr)
    simp only [Prod.fst_zero,Prod.snd_zero,
      phaseRootEnergy_origin (familyMember B eta) phi hphi (familyMember_analyticAt (hB eta heta)) (hBn eta heta),sub_zero] at hh
    have hsmall := (lt_div_iff₀ (by linarith : 0<L+1)).mp (hq.trans_le (min_le_right _ _))
    exact hh.trans (by nlinarith [norm_nonneg q])
  · intro eta heta q q' hq hq'
    exact hl eta heta q q' (hq.trans_le (min_le_left _ _)) (hq'.trans_le (min_le_left _ _))

theorem compact_family_branch (B : ℂ × E→ℂ) (phi : ℝ)
    {P : Set E} (hP : IsCompact P) (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈P,B (0,eta)≠0) :
    ∃r : ℝ,0<r ∧ ∀eta∈P,∀d : ℂ,‖d‖<r →
      AnalyticAt ℂ (familyMember B eta) (1-Complex.cos d) ∧
      B (1-Complex.cos d,eta)≠0 ∧ centralHessian (familyMember B eta) phi d≠0 := by
  let G : Set (ℂ × E) := {q | AnalyticAt ℂ B (1-Complex.cos q.1,q.2) ∧
    B (1-Complex.cos q.1,q.2)≠0 ∧ centralHessian (familyMember B q.2) phi q.1≠0}
  have hcenter (eta : E) (heta : eta∈P) : (0,eta)∈interior G := by
    apply mem_interior_iff_mem_nhds.mpr
    have ht : Tendsto (fun q : ℂ × E=>(1-Complex.cos q.1,q.2))
        (𝓝 (0,eta)) (𝓝 (0,eta)) := by
      have hh : ContinuousAt (fun q : ℂ × E=>(1-Complex.cos q.1,q.2)) (0,eta) := by fun_prop
      simpa using hh.tendsto
    exact (ht.eventually (hB eta heta).eventually_analyticAt).and
      ((ht.eventually ((hB eta heta).continuousAt.eventually_ne (hBn eta heta))).and
        ((family_hessian_analyticAt B phi eta (hB eta heta)).continuousAt.eventually_ne
          (by simp only [centralHessian_zero,ne_eq,one_ne_zero,not_false_eq_true])))
  obtain ⟨r,hr,hg⟩ := compact_product_tube hP (isOpen_interior : IsOpen (interior G)) hcenter
  refine ⟨r,hr,?_⟩
  intro eta heta d hd
  have hh := interior_subset (s:=G) (hg eta heta d hd)
  exact ⟨hh.1.comp (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const),hh.2⟩

end
end IsingBulk.Joint.Negative
