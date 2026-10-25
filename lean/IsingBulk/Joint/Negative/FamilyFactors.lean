import IsingBulk.Joint.Negative.FamilyScalar
import IsingBulk.Anisotropic.NegativeNormalForm.UniformPoleCenter

/-! Jointly analytic removable phase divided differences for a complex family.
The angular and parameter radii are fixed before the family member and n. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.First
open scoped Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Reassociation of the actual joint phase to three scalar variables. -/
theorem family_phase_increment_analyticAt (B : ℂ×E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : ScalarTriple×E=>negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2.1) (0,eta) ∧
    AnalyticAt ℂ (fun q : ScalarTriple×E=>phaseIncrement (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2) (0,eta) := by
  have ht : AnalyticAt ℂ (fun q : ScalarTriple×E=>q.1.1) (0,eta) := analyticAt_fst.comp analyticAt_fst
  have hd : AnalyticAt ℂ (fun q : ScalarTriple×E=>q.1.2.1) (0,eta) := analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have hv : AnalyticAt ℂ (fun q : ScalarTriple×E=>q.1.2.2) (0,eta) := analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)
  have he : AnalyticAt ℂ (fun q : ScalarTriple×E=>q.2) (0,eta) := analyticAt_snd
  have h0 := (familyPhase_analyticAt_center B phi hphi eta hB).fun_comp_of_eq
    (f:=fun q : ScalarTriple×E=>((q.1.1,q.1.2.1),q.2)) ((ht.prod hd).prod he) rfl
  have h1 := (familyPhase_analyticAt_center B phi hphi eta hB).fun_comp_of_eq
    (f:=fun q : ScalarTriple×E=>((q.1.1,q.1.2.1+q.1.2.2),q.2)) ((ht.prod (hd.add hv)).prod he)
    (by simp)
  exact ⟨h0,h1.sub h0⟩

theorem family_cosineFirstFactor_analyticAt (B : ℂ×E→ℂ) (eta : E)
    (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : ScalarTriple×E=>cosineFirstFactor (familyMember B q.2) q.1.2.1 q.1.1 q.1.2.2) (0,eta) := by
  have ht : AnalyticAt ℂ (fun q : ScalarTriple×E=>(q.1.1,q.2)) (0,eta) :=
    (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
  have hd : AnalyticAt ℂ (fun q : ScalarTriple×E=>q.1.2.1) (0,eta) := analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have hv : AnalyticAt ℂ (fun q : ScalarTriple×E=>q.1.2.2) (0,eta) := analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)
  exact (hB.fun_comp_of_eq ht rfl).mul
    (((Complex.analyticAt_cos.comp hd).mul
      ((zeroSlope_analyticAt Complex.analyticAt_cos).fun_comp_of_eq hv rfl)).sub
      ((Complex.analyticAt_sin.comp hd).mul
        ((zeroSlope_analyticAt Complex.analyticAt_sin).fun_comp_of_eq hv rfl)))

theorem family_cosineSecondFactor_analyticAt (B : ℂ×E→ℂ) (eta : E)
    (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : ScalarTriple×E=>cosineSecondFactor (familyMember B q.2) q.1.2.1 q.1.1 q.1.2.2) (0,eta) := by
  have ht : AnalyticAt ℂ (fun q : ScalarTriple×E=>(q.1.1,q.2)) (0,eta) :=
    (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
  have hd : AnalyticAt ℂ (fun q : ScalarTriple×E=>q.1.2.1) (0,eta) := analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have hv : AnalyticAt ℂ (fun q : ScalarTriple×E=>q.1.2.2) (0,eta) := analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)
  exact (hB.fun_comp_of_eq ht rfl).mul
    (((Complex.analyticAt_cos.comp hd).mul
      ((zeroSlope_analyticAt (zeroSlope_analyticAt Complex.analyticAt_cos)).fun_comp_of_eq hv rfl)).sub
      ((Complex.analyticAt_sin.comp hd).mul
        ((zeroSlope_analyticAt (zeroSlope_analyticAt Complex.analyticAt_sin)).fun_comp_of_eq hv rfl)))

theorem family_phaseFirstFactor_analyticAt (B : ℂ×E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : ScalarTriple×E=>phaseFirstFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2) (0,eta) := by
  obtain ⟨h0,hi⟩ := family_phase_increment_analyticAt B phi hphi eta hB
  have hden := (hyperbolicDivisor_analyticAt (negativePhase (familyMember B eta) phi hphi 0 0)).fun_comp_of_eq
    (f:=fun q : ScalarTriple×E=>(negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2.1,
      phaseIncrement (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2)) (h0.prod hi)
    (by simp [phaseIncrement])
  apply (family_cosineFirstFactor_analyticAt B eta hB).div hden
  simpa [phaseIncrement] using phase_sinh_center_ne_zero (familyMember B eta) phi hphi 0

theorem family_phaseSecondFactor_analyticAt (B : ℂ×E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : ScalarTriple×E=>phaseSecondFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2) (0,eta) := by
  obtain ⟨h0,hi⟩ := family_phase_increment_analyticAt B phi hphi eta hB
  have hs := Complex.analyticAt_sinh.comp h0
  have hden := (hyperbolicDivisor_analyticAt (negativePhase (familyMember B eta) phi hphi 0 0)).fun_comp_of_eq
    (f:=fun q : ScalarTriple×E=>(negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2.1,
      phaseIncrement (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2)) (h0.prod hi)
    (by simp [phaseIncrement])
  have hd := (hyperbolicDivisorSlope_analyticAt (negativePhase (familyMember B eta) phi hphi 0 0)).fun_comp_of_eq
    (f:=fun q : ScalarTriple×E=>(negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2.1,
      phaseIncrement (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2)) (h0.prod hi)
    (by simp [phaseIncrement])
  have ht : AnalyticAt ℂ (fun q : ScalarTriple×E=>q.1.1) (0,eta) := analyticAt_fst.comp analyticAt_fst
  have hdelta : AnalyticAt ℂ (fun q : ScalarTriple×E=>q.1.2.1) (0,eta) := analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have he : AnalyticAt ℂ (fun q : ScalarTriple×E=>q.2) (0,eta) := analyticAt_snd
  have hk0 := (family_cosineFirstFactor_analyticAt B eta hB).fun_comp_of_eq
    (f:=fun q : ScalarTriple×E=>((q.1.1,q.1.2.1,0),q.2))
    ((ht.prod (hdelta.prod analyticAt_const)).prod he) rfl
  apply (((family_cosineSecondFactor_analyticAt B eta hB).mul hs).sub
    ((hk0.mul (family_phaseFirstFactor_analyticAt B phi hphi eta hB).div_const).mul hd)).div
      (hden.mul hs)
  simpa [phaseIncrement] using mul_ne_zero
    (phase_sinh_center_ne_zero (familyMember B eta) phi hphi 0)
    (phase_sinh_center_ne_zero (familyMember B eta) phi hphi 0)

/-- Common complex-family bounds for both removable angular divisions. -/
theorem compact_family_factor_bounds (B : ℂ×E→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    {K : Set E} (hK : IsCompact K) (hB : ∀eta∈K,AnalyticAt ℂ B (0,eta)) :
    ∃r M : ℝ,0<r ∧ 0<M ∧ ∀eta∈K,∀q : ScalarTriple,‖q‖<r →
      ‖phaseFirstFactor (familyMember B eta) phi hphi q.2.1 q.1 q.2.2‖≤M ∧
      ‖phaseSecondFactor (familyMember B eta) phi hphi q.2.1 q.1 q.2.2‖≤M := by
  obtain ⟨r1,M1,hr1,hM1,hb1⟩ := compact_analytic_uniform_bound
    (fun q : ScalarTriple×E=>phaseFirstFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2)
    hK (fun eta heta=>family_phaseFirstFactor_analyticAt B phi hphi eta (hB eta heta))
  obtain ⟨r2,M2,hr2,hM2,hb2⟩ := compact_analytic_uniform_bound
    (fun q : ScalarTriple×E=>phaseSecondFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2)
    hK (fun eta heta=>family_phaseSecondFactor_analyticAt B phi hphi eta (hB eta heta))
  refine ⟨min r1 r2,max M1 M2,lt_min hr1 hr2,hM1.trans_le (le_max_left _ _),?_⟩
  intro eta heta q hq
  exact ⟨((hb1 eta heta q (hq.trans_le (min_le_left _ _))).2.le.trans (le_max_left _ _)),
    ((hb2 eta heta q (hq.trans_le (min_le_right _ _))).2.le.trans (le_max_right _ _))⟩

end
end IsingBulk.Joint.Negative
