import IsingBulk.Joint.Negative.FamilyQuadratic
import IsingBulk.Joint.Negative.FamilyScalar
import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueSlope
import IsingBulk.Anisotropic.NegativeNormalForm.DensityResiduePrefactor

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Metric Filter IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1200000

/-- A common moving-center quadratic estimate. The compact parameter is genuinely complex. -/
theorem compact_family_even_moving_center_control (S : ScalarTriple × E → ℂ)
    {K : Set E} (hK : IsCompact K) (hS : ∀ eta ∈ K, AnalyticAt ℂ S (0,eta))
    (heven : ∀ eta ∈ K, ∀ t v : ℂ, S ((t,(0,-v)),eta)=S ((t,(0,v)),eta)) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ eta ∈ K, ∀ t t₀ d x : ℂ,
      ‖t‖<r → ‖t₀‖<r → ‖d‖<r → ‖x‖<r →
      ‖S ((t,(d,x)),eta)-S ((t₀,(d,0)),eta)‖ ≤
        L*(‖t-t₀‖+(‖d‖+‖x‖)*‖x‖) := by
  obtain ⟨r,L,hr,hL,hquad⟩ := compact_family_even_quadratic S hK hS heven
  obtain ⟨s,M,N,hs,hM,_hN,_ha,hLip⟩ := compact_analytic_uniform_lipschitz S hK hS
  refine ⟨min r s,L+M,lt_min hr hs,by positivity,?_⟩
  intro eta heta t t₀ d x ht ht₀ hd hx
  have hp : ‖(t,(d,x))‖<r := (max_lt ht (max_lt hd hx)).trans_le (min_le_left _ _)
  have hbase : ‖(t,(d,(0:ℂ)))‖<s := by
    simpa [Prod.norm_def] using (max_lt ht hd).trans_le (min_le_right r s)
  have hbase₀ : ‖(t₀,(d,(0:ℂ)))‖<s := by
    simpa [Prod.norm_def] using (max_lt ht₀ hd).trans_le (min_le_right r s)
  have hparam := hLip eta heta (t,(d,0)) (t₀,(d,0)) hbase hbase₀
  have hdiff : ‖(t,(d,(0:ℂ)))-(t₀,(d,0))‖=‖t-t₀‖ := by simp [Prod.norm_def]
  rw [hdiff] at hparam
  calc
    _ ≤ ‖S ((t,(d,x)),eta)-S ((t,(d,0)),eta)‖+
        ‖S ((t,(d,0)),eta)-S ((t₀,(d,0)),eta)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ L*(‖d‖+‖x‖)*‖x‖+M*‖t-t₀‖ := add_le_add (hquad eta heta _ hp) hparam
    _ ≤ _ := by nlinarith [mul_nonneg hL.le (norm_nonneg (t-t₀)),
      mul_nonneg hM.le (mul_nonneg (add_nonneg (norm_nonneg d) (norm_nonneg x)) (norm_nonneg x))]

theorem compact_family_parameter_nonzero (f : ℂ × E → ℂ) {K : Set E}
    (hK : IsCompact K) (hf : ∀ eta ∈ K, AnalyticAt ℂ f (0,eta))
    (hf0 : ∀ eta ∈ K, f (0,eta) ≠ 0) :
    ∃ r : ℝ, 0<r ∧ ∀ eta ∈ K, ∀ t : ℂ, ‖t‖<r →
      AnalyticAt ℂ f (t,eta) ∧ f (t,eta)≠0 := by
  let U : Set (ℂ × E) := {q | AnalyticAt ℂ f q ∧ f q ≠ 0}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    exact hq.1.eventually_analyticAt.and (hq.1.continuousAt.eventually_ne hq.2)
  exact compact_product_tube hK hU (fun eta heta => ⟨hf eta heta,hf0 eta heta⟩)

/-- Actual scalar ratios, including B and a supplied rootB, on a common parameter disk. -/
theorem compact_family_parameter_ratio_control (f : ℂ × E → ℂ) {K : Set E}
    (hK : IsCompact K) (hf : ∀ eta ∈ K, AnalyticAt ℂ f (0,eta))
    (hf0 : ∀ eta ∈ K, f (0,eta) ≠ 0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ eta ∈ K, ∀ t t₀ : ℂ, ‖t‖<r → ‖t₀‖<r →
      f (t₀,eta)≠0 ∧ ‖f (t,eta)/f (t₀,eta)-1‖≤L*‖t-t₀‖ := by
  let F : (ℂ × ℂ) × E → ℂ := fun q => f (q.1.1,q.2)/f (q.1.2,q.2)
  have hF (eta : E) (heta : eta∈K) : AnalyticAt ℂ F (0,eta) :=
    ((hf eta heta).comp (f:=fun q : (ℂ × ℂ) × E => (q.1.1,q.2))
      ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)).div
    ((hf eta heta).comp (f:=fun q : (ℂ × ℂ) × E => (q.1.2,q.2))
      ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)) (hf0 eta heta)
  obtain ⟨r,L,M,hr,hL,_hM,_ha,hLip⟩ := compact_analytic_uniform_lipschitz F hK hF
  obtain ⟨s,hs,hn⟩ := compact_family_parameter_nonzero f hK hf hf0
  refine ⟨min r s,L,lt_min hr hs,hL,?_⟩
  intro eta heta t t₀ ht ht₀
  have hnt := (hn eta heta t₀ (ht₀.trans_le (min_le_right _ _))).2
  refine ⟨hnt,?_⟩
  have hh := hLip eta heta (t,t₀) (t₀,t₀)
    ((max_lt ht ht₀).trans_le (min_le_left _ _))
    (by simpa using ht₀.trans_le (min_le_left r s))
  simpa [F,div_self hnt,Prod.norm_def] using hh

theorem family_negativePhase_moving_analyticAt (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : ScalarTriple × E =>
      negativePhase (familyMember B q.2) phi hphi q.1.1 (q.1.2.1+q.1.2.2)) (0,eta) := by
  apply (familyPhase_analyticAt_center B phi hphi eta hB).comp_of_eq
    (f:=fun q : ScalarTriple × E => ((q.1.1,q.1.2.1+q.1.2.2),q.2))
  · exact ((analyticAt_fst.comp analyticAt_fst).prod
      ((analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)).add
        (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)))).prod analyticAt_snd
  · simp

theorem compact_family_negativePhase_moving_center_control (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ eta ∈ K, ∀ t d x : ℂ,
      ‖t‖<r → ‖1-Complex.cos d‖<r → ‖d‖<r → ‖x‖<r →
      ‖negativePhase (familyMember B eta) phi hphi t (d+x)-(phi:ℂ)*Complex.I‖ ≤
        L*(‖t-(1-Complex.cos d)‖+(‖d‖+‖x‖)*‖x‖) := by
  obtain ⟨r,L,hr,hL,h⟩ := compact_family_even_moving_center_control _ hK
    (fun eta heta => family_negativePhase_moving_analyticAt B phi hphi eta (hB eta heta))
    (fun eta _ t v => by simpa using negativePhase_even (familyMember B eta) phi hphi t v)
  refine ⟨r,L,hr,hL,?_⟩
  intro eta heta t d x ht ht₀ hd hx
  simpa only [add_zero,negativePhase_center] using h eta heta t (1-Complex.cos d) d x ht ht₀ hd hx

theorem compact_family_residueOneBodyRatio_control (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ eta ∈ K, ∀ t d x : ℂ,
      ‖t‖<r → ‖1-Complex.cos d‖<r → ‖d‖<r → ‖x‖<r →
      ‖residueOneBodyRatio (familyMember B eta) phi hphi (t,(d,x))-1‖ ≤
        L*(‖t-(1-Complex.cos d)‖+(‖d‖+‖x‖)*‖x‖) := by
  have ha (eta : E) (heta : eta∈K) : AnalyticAt ℂ
      (fun q : ScalarTriple × E => residueOneBodyRatio (familyMember B q.2) phi hphi q.1) (0,eta) :=
    analyticAt_const.div (Complex.analyticAt_sinh.comp
      (family_negativePhase_moving_analyticAt B phi hphi eta (hB eta heta)))
      (by simpa using phase_sinh_center_ne_zero (familyMember B eta) phi hphi 0)
  obtain ⟨r,L,hr,hL,h⟩ := compact_family_even_moving_center_control _ hK ha
    (fun eta _ t v => by simp [residueOneBodyRatio,negativePhase_even])
  refine ⟨r,L,hr,hL,?_⟩
  intro eta heta t d x ht ht₀ hd hx
  simpa only [residueOneBodyRatio_center] using h eta heta t (1-Complex.cos d) d x ht ht₀ hd hx

end
end IsingBulk.Joint.Negative
