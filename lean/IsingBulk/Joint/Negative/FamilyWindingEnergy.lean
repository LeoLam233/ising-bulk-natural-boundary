import IsingBulk.Joint.Negative.FamilyEnergy
import IsingBulk.Anisotropic.NegativeDominance.RealPoleLowerBound

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1200000

theorem compact_family_real_pole_energy_lower (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hB0 : ∀eta∈Q,B (0,eta)≠0) :
    ∃ δ : ℝ,0<δ ∧ ∀eta∈Q,∀ n : ℕ, n≠0 → ∀ d : ℝ, ∀ t : ℂ, ∀ v : Fin n → ℝ,
      |d|<δ → ‖t‖<δ → (∀ i, |v i|<δ) →
      ZeroMean (fun i => (v i : ℂ)) →
      poleEquation (familyMember B eta) phi hphi (d : ℂ) t (fun i => (v i : ℂ))=0 →
      1-Real.cos d+(∑ i,(v i)^2)/(4*(n : ℝ))≤t.re := by
  let energy : ScalarTriple × E→ℂ := fun q=>
    centralHessian (familyMember B q.2) phi q.1.2.1*
      phaseEnergy (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2
  let G : Set (ScalarTriple × E) := {q |
    centralHessian (familyMember B q.2) phi q.1.2.1≠0 ∧
    phaseParameterQuotient (familyMember B q.2) phi hphi q.1.2.1 q.1.1≠0 ∧ ‖energy q-1‖<1/2}
  have hcenter (eta : E) (heta : eta∈Q) : (0,eta)∈interior G := by
    have hh := family_hessian_analyticAt B phi eta (hB eta heta)
    have hq := family_parameterQuotient_analyticAt B phi hphi eta (hB eta heta)
    have hq0 : phaseParameterQuotient (familyMember B eta) phi hphi 0 0≠0 := by
      have he := phaseParameterQuotient_center (familyMember B eta) phi hphi 0
        (by simpa using familyMember_analyticAt (hB eta heta))
      simp only [Complex.cos_zero,sub_self] at he
      rw [he]
      exact mul_ne_zero (inv_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hphi) Complex.I_ne_zero)) (hB0 eta heta)
    have hha : AnalyticAt ℂ (fun q : ScalarTriple × E=>centralHessian (familyMember B q.2) phi q.1.2.1) (0,eta) :=
      hh.comp_of_eq (f:=fun q : ScalarTriple × E=>(q.1.2.1,q.2))
        ((analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)).prod analyticAt_snd) rfl
    have hqa : AnalyticAt ℂ (fun q : ScalarTriple × E=>phaseParameterQuotient (familyMember B q.2) phi hphi q.1.2.1 q.1.1) (0,eta) :=
      hq.comp_of_eq (f:=fun q : ScalarTriple × E=>((q.1.1,q.1.2.1),q.2))
        (((analyticAt_fst.comp analyticAt_fst).prod
          (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst))).prod analyticAt_snd) rfl
    have hEa : AnalyticAt ℂ energy (0,eta) := hha.mul
      (family_energy_analyticAt B phi hphi eta (hB eta heta) (hB0 eta heta))
    have hE0 : energy (0,eta)=1 := by
      have he := phaseEnergy_center (familyMember B eta) phi hphi 0
        (by simpa using familyMember_analyticAt (hB eta heta)) (by simpa [familyMember] using hB0 eta heta)
        (by simp [centralHessian_zero])
      simpa only [energy,Prod.fst_zero,Prod.snd_zero,centralHessian_zero,Complex.cos_zero,sub_self,one_mul] using he
    apply mem_interior_iff_mem_nhds.mpr
    exact (hha.continuousAt.eventually_ne (by change centralHessian (familyMember B eta) phi 0≠0; simp only [centralHessian_zero,ne_eq,one_ne_zero,not_false_eq_true])).and
      ((hqa.continuousAt.eventually_ne hq0).and
        ((hEa.continuousAt.sub continuousAt_const).norm.eventually_lt_const (by change ‖energy (0,eta)-1‖<(1/2:ℝ); rw [hE0,sub_self,norm_zero]; norm_num)))
  obtain ⟨δ,hδ,htube⟩ := compact_product_tube (X:=ScalarTriple) hQ
    (isOpen_interior : IsOpen (interior G)) hcenter
  refine ⟨δ,hδ,?_⟩
  intro eta heta n hn d t v hd ht hv hmean hpole
  let E : ScalarTriple→ℂ := fun p=>energy (p,eta)
  have hball {p : ScalarTriple} (hp : p∈ball 0 δ) :
      centralHessian (familyMember B eta) phi p.2.1≠0 ∧
      phaseParameterQuotient (familyMember B eta) phi hphi p.2.1 p.1≠0 ∧ ‖E p-1‖≤1/2 := by
    have hm : (p,eta)∈interior G := htube eta heta p (by simpa using hp)
    have hg : (p,eta)∈G := interior_subset hm
    exact ⟨hg.1,hg.2.1,hg.2.2.le⟩
  have hmem (x : ℝ) (hx : |x|<δ) : (t,((d : ℂ),(x : ℂ)))∈ball (0 : ScalarTriple) δ := by
    simpa only [mem_ball,dist_zero_right,Prod.norm_def,Complex.norm_real,Real.norm_eq_abs,max_lt_iff]
      using And.intro ht (And.intro hd hx)
  have hbase := hball (hmem 0 (by simpa using hδ))
  have hex := phaseSeparableMap_exact hn (familyMember B eta) phi hphi (d : ℂ) t (fun i => (v i : ℂ))
    hmean hbase.1 hbase.2.1 hpole
  rw [phaseSeparableMap,quadratic_separableMap] at hex
  have hnc : (n : ℂ)≠0 := by exact_mod_cast hn
  have henergy : (2*(n : ℂ))*(t-(1-Complex.cos (d : ℂ)))=
      ∑ i,(v i : ℂ)^2*E (t,((d : ℂ),(v i : ℂ))) := by
    rw [hex]
    calc
      _ = centralHessian (familyMember B eta) phi (d : ℂ)*
          ∑ i,(v i : ℂ)^2*phaseEnergy (familyMember B eta) phi hphi (d : ℂ) t (v i : ℂ) := by
        field_simp
        rfl
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [E,energy]
        ring
  rw [show (2 : ℂ)*(n : ℂ)=((2*(n : ℝ) : ℝ) : ℂ) by push_cast; rfl] at henergy
  simp only [←Complex.ofReal_pow] at henergy
  have hreal := congrArg Complex.re henergy
  simp [Complex.mul_re] at hreal
  simp only [←Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
    Finset.sum_const_zero,sub_zero,Complex.cos_ofReal_re] at hreal
  have hEreal (i : Fin n) : (1/2 : ℝ)≤(E (t,((d : ℂ),(v i : ℂ)))).re := by
    have he' := (hball (hmem (v i) (hv i))).2.2
    have hab := (Complex.abs_re_le_norm (E (t,((d : ℂ),(v i : ℂ)))-1)).trans he'
    simp only [Complex.sub_re,Complex.one_re] at hab
    linarith [(abs_le.mp hab).1]
  have hsum : (∑ i,(v i)^2)/2≤∑ i,(v i)^2*(E (t,((d : ℂ),(v i : ℂ)))).re := by
    calc
      _ = ∑ i,(v i)^2*(1/2 : ℝ) := by rw [←Finset.sum_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hEreal i) (sq_nonneg _))
  have hnR : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hdiv : (∑ i,(v i)^2)/(4*(n : ℝ))≤t.re-(1-Real.cos d) := by
    apply (div_le_iff₀ (by positivity : 0<4*(n : ℝ))).mpr
    nlinarith only [hreal,hsum]
  linarith


end
end IsingBulk.Joint.Negative
