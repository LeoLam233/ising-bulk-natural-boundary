import IsingBulk.Joint.Negative.FamilyFactors

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Both removable division identities hold jointly with the complex family
parameter, not only on each individual real slice. -/
theorem family_factors_eventually (B : ℂ×E→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (eta : E) (hB : AnalyticAt ℂ B (0,eta)) :
    ∀ᶠq : ScalarTriple×E in 𝓝 (0,eta),
      phaseIncrement (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2=
        q.1.2.2*phaseFirstFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2 ∧
      phaseFirstFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2-
        phaseFirstFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 0=
        q.1.2.2*phaseSecondFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2 := by
  have hWa : AnalyticAt ℂ
      (fun q : (ℂ × ℂ) × E=>negativeDispersion (familyMember B q.2) (Real.cos phi) q.1.1 q.1.2) ((0,0),eta) := by
    have ht : AnalyticAt ℂ (fun q : (ℂ × ℂ) × E=>q.1.1) ((0,0),eta) := analyticAt_fst.comp analyticAt_fst
    have hd : AnalyticAt ℂ (fun q : (ℂ × ℂ) × E=>q.1.2) ((0,0),eta) := analyticAt_snd.comp analyticAt_fst
    exact analyticAt_const.add ((hB.comp (f:=fun q : (ℂ × ℂ) × E=>(q.1.1,q.2)) (ht.prod analyticAt_snd)).mul
      ((ht.sub analyticAt_const).add (Complex.analyticAt_cos.comp hd)))
  have hcosh : ∀ᶠq : (ℂ × ℂ) × E in 𝓝 ((0,0),eta),
      Complex.cosh (negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2)=
        negativeDispersion (familyMember B q.2) (Real.cos phi) q.1.1 q.1.2 := by
    have hc := hWa.continuousAt.tendsto
    have hW0 : negativeDispersion (familyMember B eta) (Real.cos phi) 0 0=(Real.cos phi:ℂ) := by
      simp [negativeDispersion]
    rw [hW0] at hc
    exact hc.eventually (edgePhase_spec phi hphi).2.2.1
  have hbase : ContinuousAt (fun q : ScalarTriple×E=>((q.1.1,q.1.2.1),q.2)) (0,eta) := by fun_prop
  have hshift : ContinuousAt (fun q : ScalarTriple×E=>((q.1.1,q.1.2.1+q.1.2.2),q.2)) (0,eta) := by fun_prop
  have he0 := hbase.tendsto.eventually hcosh
  have hshift' : Tendsto (fun q : ScalarTriple×E=>((q.1.1,q.1.2.1+q.1.2.2),q.2))
      (𝓝 (0,eta)) (𝓝 (((0:ℂ),0),eta)) := by simpa using hshift.tendsto
  have he1 := hshift'.eventually hcosh
  obtain ⟨h0,hi⟩ := family_phase_increment_analyticAt B phi hphi eta hB
  have hden := (hyperbolicDivisor_analyticAt (negativePhase (familyMember B eta) phi hphi 0 0)).fun_comp_of_eq
    (f:=fun q : ScalarTriple×E=>(negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2.1,
      phaseIncrement (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2)) (h0.prod hi)
    (by simp [phaseIncrement])
  have hs0 : Complex.sinh (negativePhase (familyMember B eta) phi hphi 0 0)≠0 := by
    simpa using phase_sinh_center_ne_zero (familyMember B eta) phi hphi 0
  have hde := hden.continuousAt.eventually_ne (by simpa [phaseIncrement] using hs0)
  have hse := (Complex.continuous_sinh.continuousAt.comp h0.continuousAt).eventually_ne hs0
  filter_upwards [he0,he1,hde,hse] with q hq0 hq1 hd hs
  have hfirst := phaseFirstFactor_identity (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2 hq0 hq1 hd
  exact ⟨hfirst,phaseSecondFactor_identity (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2 hfirst hd hs⟩

/-- One common scalar tridisk carries the exact phase identities for the
entire compact complex family. -/
theorem compact_family_factor_identities (B : ℂ×E→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    {K : Set E} (hK : IsCompact K) (hB : ∀eta∈K,AnalyticAt ℂ B (0,eta)) :
    ∃r : ℝ,0<r ∧ ∀eta∈K,∀q : ScalarTriple,‖q‖<r →
      phaseIncrement (familyMember B eta) phi hphi q.2.1 q.1 q.2.2=
        q.2.2*phaseFirstFactor (familyMember B eta) phi hphi q.2.1 q.1 q.2.2 ∧
      phaseFirstFactor (familyMember B eta) phi hphi q.2.1 q.1 q.2.2-
        phaseFirstFactor (familyMember B eta) phi hphi q.2.1 q.1 0=
        q.2.2*phaseSecondFactor (familyMember B eta) phi hphi q.2.1 q.1 q.2.2 := by
  let G : Set (ScalarTriple×E) := {q |
    phaseIncrement (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2=
      q.1.2.2*phaseFirstFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2 ∧
    phaseFirstFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2-
      phaseFirstFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 0=
      q.1.2.2*phaseSecondFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2}
  obtain ⟨r,hr,hball⟩ := compact_product_tube hK (isOpen_interior : IsOpen (interior G)) (by
    intro eta heta
    exact mem_interior_iff_mem_nhds.mpr (family_factors_eventually B phi hphi eta (hB eta heta)))
  exact ⟨r,hr,fun eta heta q hq=>(interior_subset (s:=G) (hball eta heta q hq))⟩

end
end IsingBulk.Joint.Negative
