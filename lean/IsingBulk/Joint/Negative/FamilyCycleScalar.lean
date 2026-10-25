import IsingBulk.Joint.Negative.FamilyScalar
import IsingBulk.Anisotropic.NegativeCycles.JointDensityAnalytic

/-! Joint scalar analytic factors for compact-family Stokes transport. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeCycles
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 theorem family_cycle_oneBody_analyticAt (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {eta : E} (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : (ℂ × ℂ) × E =>
      (Complex.sinh (negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2))⁻¹) ((0,0),eta) := by
  apply (Complex.analyticAt_sinh.comp (familyPhase_analyticAt_center B phi hphi eta hB)).inv
  have hz : negativePhase (familyMember B eta) phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa using negativePhase_center (familyMember B eta) phi hphi 0
  change Complex.sinh (negativePhase (familyMember B eta) phi hphi 0 0)≠0
  rw [hz,Complex.sinh_mul_I,←Complex.ofReal_sin]
  exact mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero

theorem family_cycle_pair_analyticAt (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {eta : E} (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : (ℂ × ℂ × ℂ) × E =>
      localCompletePair (familyMember B q.2) phi hphi q.1.1 q.1.2.1 q.1.2.2) (0,eta) := by
  have hg := familyPhase_analyticAt_center B phi hphi eta hB
  have ht : AnalyticAt ℂ (fun q : (ℂ × ℂ × ℂ) × E => q.1.1) (0,eta) := analyticAt_fst.comp analyticAt_fst
  have ha : AnalyticAt ℂ (fun q : (ℂ × ℂ × ℂ) × E => q.1.2.1) (0,eta) := analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have hb : AnalyticAt ℂ (fun q : (ℂ × ℂ × ℂ) × E => q.1.2.2) (0,eta) := analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)
  have h1 : AnalyticAt ℂ (fun q : (ℂ × ℂ × ℂ) × E => negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2.1) (0,eta) :=
    hg.comp_of_eq (f := fun q : (ℂ × ℂ × ℂ) × E => ((q.1.1,q.1.2.1),q.2))
      ((ht.prod ha).prod analyticAt_snd) rfl
  have h2 : AnalyticAt ℂ (fun q : (ℂ × ℂ × ℂ) × E => negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2.2) (0,eta) :=
    hg.comp_of_eq (f := fun q : (ℂ × ℂ × ℂ) × E => ((q.1.1,q.1.2.2),q.2))
      ((ht.prod hb).prod analyticAt_snd) rfl
  have hz : negativePhase (familyMember B eta) phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa using negativePhase_center (familyMember B eta) phi hphi 0
  have hden : Complex.sinh ((negativePhase (familyMember B eta) phi hphi 0 0+
      negativePhase (familyMember B eta) phi hphi 0 0)/2)≠0 := by
    rw [hz,show ((phi:ℂ)*Complex.I+(phi:ℂ)*Complex.I)/2=(phi:ℂ)*Complex.I by ring,
      Complex.sinh_mul_I,←Complex.ofReal_sin]
    exact mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero
  exact (hB.comp_of_eq (f := fun q : (ℂ × ℂ × ℂ) × E => (q.1.1,q.2))
    (ht.prod analyticAt_snd) rfl).mul
    (((Complex.analyticAt_sin.comp ((ha.sub hb).div_const)).div
      (Complex.analyticAt_sinh.comp ((h1.add h2).div_const)) hden).pow 2)

/-- All scalar factors are analytic on one tube before the family member or
particle dimension is selected. -/
theorem compact_family_cycle_scalar_analytic (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta)) :
    ∃ r : ℝ, 0<r ∧ ∀ eta∈Q,
      (∀ t : ℂ, ‖t‖<r → AnalyticAt ℂ (familyMember B eta) t ∧ AnalyticAt ℂ (familyMember rootB eta) t) ∧
      (∀ t a : ℂ, ‖t‖<r → ‖a‖<r →
        AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase (familyMember B eta) phi hphi z.1 z.2) (t,a) ∧
        AnalyticAt ℂ (fun z : ℂ × ℂ => (Complex.sinh (negativePhase (familyMember B eta) phi hphi z.1 z.2))⁻¹) (t,a)) ∧
      (∀ t a b : ℂ, ‖t‖<r → ‖a‖<r → ‖b‖<r →
        AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => localCompletePair (familyMember B eta) phi hphi z.1 z.2.1 z.2.2) (t,a,b)) := by
  obtain ⟨r₀,hr₀,h₀⟩ := compact_product_tube hQ
    ((isOpen_analyticAt ℂ B).inter (isOpen_analyticAt ℂ rootB)) (fun eta heta => ⟨hB eta heta,hroot eta heta⟩)
  obtain ⟨r₁,hr₁,h₁⟩ := compact_product_tube hQ
    ((isOpen_analyticAt ℂ (familyPhase B phi hphi)).inter
      (isOpen_analyticAt ℂ (fun q : (ℂ × ℂ) × E =>
        (Complex.sinh (negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2))⁻¹)))
    (fun eta heta => ⟨familyPhase_analyticAt_center B phi hphi eta (hB eta heta),family_cycle_oneBody_analyticAt B phi hphi (hB eta heta)⟩)
  obtain ⟨r₂,hr₂,h₂⟩ := compact_product_tube hQ
    (isOpen_analyticAt ℂ (fun q : (ℂ × ℂ × ℂ) × E =>
      localCompletePair (familyMember B q.2) phi hphi q.1.1 q.1.2.1 q.1.2.2))
    (fun eta heta => family_cycle_pair_analyticAt B phi hphi (hB eta heta))
  refine ⟨min r₀ (min r₁ r₂),lt_min hr₀ (lt_min hr₁ hr₂),?_⟩
  intro eta heta
  refine ⟨?_,?_,?_⟩
  · intro t ht
    have hh := h₀ eta heta t (ht.trans_le (min_le_left _ _))
    exact ⟨hh.1.comp (f := fun t : ℂ => (t,eta)) (analyticAt_id.prod analyticAt_const),
      hh.2.comp (f := fun t : ℂ => (t,eta)) (analyticAt_id.prod analyticAt_const)⟩
  · intro t a ht ha
    have hh := h₁ eta heta (t,a) ((max_lt ht ha).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    exact ⟨hh.1.comp (f := fun z : ℂ × ℂ => (z,eta)) (analyticAt_id.prod analyticAt_const),
      hh.2.comp (f := fun z : ℂ × ℂ => (z,eta)) (analyticAt_id.prod analyticAt_const)⟩
  · intro t a b ht ha hb
    have hh := h₂ eta heta (t,a,b) ((max_lt ht (max_lt ha hb)).trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact hh.comp (f := fun z : ℂ × ℂ × ℂ => (z,eta)) (analyticAt_id.prod analyticAt_const)

end
end IsingBulk.Joint.Negative
