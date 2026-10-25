import IsingBulk.Joint.Negative.FamilyScalar
import IsingBulk.Joint.Negative.CompactAnalyticBounds
import IsingBulk.Anisotropic.NegativeDominance.RegularNumeratorBound

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeCycles IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem family_oneBody_analyticAt (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : (ℂ × ℂ) × E=>(Complex.sinh
      (negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2))⁻¹) ((0,0),eta) := by
  apply (Complex.analyticAt_sinh.comp (familyPhase_analyticAt_center B phi hphi eta hB)).inv
  have hz : negativePhase (familyMember B eta) phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa using negativePhase_center (familyMember B eta) phi hphi 0
  change Complex.sinh (negativePhase (familyMember B eta) phi hphi 0 0)≠0
  rw [hz,Complex.sinh_mul_I,←Complex.ofReal_sin]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hphi) Complex.I_ne_zero

theorem compact_family_complex_factors (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hr : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta)) :
    ∃δ M : ℝ,0<δ ∧ 1≤M ∧ ∀eta∈Q,∀t a : ℂ,‖t‖<δ → ‖a‖<δ →
      ‖B (t,eta)‖≤M ∧ ‖rootB (t,eta)‖≤M ∧
      ‖(Complex.sinh (negativePhase (familyMember B eta) phi hphi t a))⁻¹‖≤M := by
  let f : (ℂ × ℂ) × E→ℂ × (ℂ × ℂ) := fun q=>(B (q.1.1,q.2),rootB (q.1.1,q.2),
    (Complex.sinh (negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2))⁻¹)
  have hf (eta : E) (heta : eta∈Q) : AnalyticAt ℂ f ((0,0),eta) := by
    have hm : AnalyticAt ℂ (fun q : (ℂ × ℂ) × E=>(q.1.1,q.2)) ((0,0),eta) :=
      (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
    exact ((hB eta heta).comp_of_eq (f:=fun q : (ℂ × ℂ) × E=>(q.1.1,q.2)) hm rfl).prod (((hr eta heta).comp_of_eq (f:=fun q : (ℂ × ℂ) × E=>(q.1.1,q.2)) hm rfl).prod
      (family_oneBody_analyticAt B phi hphi eta (hB eta heta)))
  obtain ⟨δ,M,hδ,_hM,hbound⟩ := compact_analytic_uniform_bound f hQ hf
  refine ⟨δ,max 1 M,hδ,le_max_left _ _,?_⟩
  intro eta heta t a ht ha
  have hh := (hbound eta heta (t,a) (max_lt ht ha)).2.le
  change max ‖B (t,eta)‖ (max ‖rootB (t,eta)‖ ‖(Complex.sinh (negativePhase (familyMember B eta) phi hphi t a))⁻¹‖)≤M at hh
  exact ⟨((le_max_left _ _).trans hh).trans (le_max_right _ _),
    ((le_max_left _ _).trans ((le_max_right _ _).trans hh)).trans (le_max_right _ _),
    ((le_max_right _ _).trans ((le_max_right _ _).trans hh)).trans (le_max_right _ _)⟩

theorem family_regularAngularPair_analyticAt (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta)) :
    AnalyticAt ℂ (fun q : ScalarTriple × E=>regularAngularPair (familyMember B q.2) phi hphi
      q.1.1 q.1.2.1 q.1.2.2) (0,eta) := by
  have hg := familyPhase_analyticAt_center B phi hphi eta hB
  have ht : AnalyticAt ℂ (fun q : ScalarTriple × E=>q.1.1) (0,eta) := analyticAt_fst.comp analyticAt_fst
  have ha : AnalyticAt ℂ (fun q : ScalarTriple × E=>q.1.2.1) (0,eta) := analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have hb : AnalyticAt ℂ (fun q : ScalarTriple × E=>q.1.2.2) (0,eta) := analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)
  have h1 := hg.comp_of_eq (f:=fun q : ScalarTriple × E=>((q.1.1,q.1.2.1),q.2))
    ((ht.prod ha).prod analyticAt_snd) rfl
  have h2 := hg.comp_of_eq (f:=fun q : ScalarTriple × E=>((q.1.1,q.1.2.2),q.2))
    ((ht.prod hb).prod analyticAt_snd) rfl
  have hz : negativePhase (familyMember B eta) phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa using negativePhase_center (familyMember B eta) phi hphi 0
  have hden : Complex.sinh ((negativePhase (familyMember B eta) phi hphi 0 0+
      negativePhase (familyMember B eta) phi hphi 0 0)/2)≠0 := by
    rw [hz,show ((phi:ℂ)*Complex.I+(phi:ℂ)*Complex.I)/2=(phi:ℂ)*Complex.I by ring]
    rw [Complex.sinh_mul_I,←Complex.ofReal_sin]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hphi) Complex.I_ne_zero
  exact ((halfSineSlope_analyticAt.comp_of_eq (ha.sub hb) (by simp)).div
    (Complex.analyticAt_sinh.comp ((h1.add h2).div_const)) hden).pow 2

theorem compact_family_regularAngularPair_bound (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) :
    ∃δ M : ℝ,0<δ ∧ 1≤M ∧ ∀eta∈Q,∀t a b : ℂ,‖t‖<δ → ‖a‖<δ → ‖b‖<δ →
      ‖regularAngularPair (familyMember B eta) phi hphi t a b‖≤M := by
  obtain ⟨δ,M,hδ,_hM,hbound⟩ := compact_analytic_uniform_bound
    (fun q : ScalarTriple × E=>regularAngularPair (familyMember B q.2) phi hphi q.1.1 q.1.2.1 q.1.2.2)
    hQ (fun eta heta=>family_regularAngularPair_analyticAt B phi hphi eta (hB eta heta))
  exact ⟨δ,max 1 M,hδ,le_max_left _ _,fun eta heta t a b ht ha hb=>
    ((hbound eta heta (t,(a,b)) (max_lt ht (max_lt ha hb))).2.le).trans (le_max_right _ _)⟩

/-- Coarse but genuine dimension-uniform full-density bound retaining every
Vandermonde zero. Its exponential N² cost is sufficient in the high range. -/
theorem compact_family_numerator_vandermonde_bound (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hr : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta)) :
    ∃ δ M : ℝ,0<δ ∧ 1≤M ∧ ∀eta∈Q,∀n : ℕ, ∀d t : ℂ, ∀v : Config n,
      ‖d‖<δ → ‖t‖<δ → (∀i, ‖v i‖<δ) →
      ‖formFactorNumerator (familyMember B eta) (familyMember rootB eta) phi hphi d t v‖≤
        ‖vandermonde v‖^2*M^(1+alpha n+n+n.choose 2) := by
  obtain ⟨δ₁,M₁,hδ₁,hM₁,hscalar⟩ := compact_family_complex_factors B rootB phi hphi hQ hB hr
  obtain ⟨δ₂,M₂,hδ₂,hM₂,hpair⟩ := compact_family_regularAngularPair_bound B phi hphi hQ hB
  let δ := min δ₁ δ₂ / 2
  let M := max M₁ M₂
  have hδ : 0<δ := div_pos (lt_min hδ₁ hδ₂) (by norm_num)
  have hδ1 : 2*δ≤δ₁ := by dsimp [δ]; linarith [min_le_left δ₁ δ₂]
  have hδ2 : 2*δ≤δ₂ := by dsimp [δ]; linarith [min_le_right δ₁ δ₂]
  have hM : 1≤M := hM₁.trans (le_max_left _ _)
  refine ⟨δ,M,hδ,hM,?_⟩
  intro eta heta n d t v hd ht hv
  have ht1 : ‖t‖<δ₁ := by linarith
  have ht2 : ‖t‖<δ₂ := by linarith
  have ha (i) : ‖d+v i‖<2*δ := (norm_add_le d (v i)).trans_lt (by linarith [hv i])
  have hs := hscalar eta heta t 0 ht1 (by simpa using hδ₁)
  have hh := regularNumerator_norm_bound (familyMember B eta) (familyMember rootB eta) phi hphi d t v hM
    (hs.1.trans (le_max_left _ _)) (hs.2.1.trans (le_max_left _ _))
    (fun i => ((hscalar eta heta t (d+v i) ht1 ((ha i).trans_le hδ1)).2.2).trans (le_max_left _ _))
    (fun i j => (hpair eta heta t (d+v i) (d+v j) ht2 ((ha i).trans_le hδ2) ((ha j).trans_le hδ2)).trans (le_max_right _ _))
  rw [formFactorNumerator_factor,norm_mul,norm_pow]
  exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)

end
end IsingBulk.Joint.Negative
