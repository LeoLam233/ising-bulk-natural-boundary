import IsingBulk.Joint.Negative.FamilyScalar
import IsingBulk.Joint.Negative.CompactAnalyticBounds
import IsingBulk.Anisotropic.NegativeCycles.ActualResidueSlope

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeCycles
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_family_central_slope_lower (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hB0 : ∀eta∈Q,B (0,eta)≠0) :
    ∃c : ℝ,0<c ∧ ∀eta∈Q,c≤‖centralParameterSlope (familyMember B eta) phi 0‖ := by
  let f : ℂ × E→ℂ := fun q=>(centralParameterSlope (familyMember B q.2) phi 0)⁻¹
  have hfa (eta : E) (heta : eta∈Q) : AnalyticAt ℂ f (0,eta) := by
    have hb : AnalyticAt ℂ (fun q : ℂ × E=>B (0,q.2)) (0,eta) :=
      (hB eta heta).comp_of_eq (f:=fun q : ℂ × E=>((0:ℂ),q.2))
        (analyticAt_const.prod analyticAt_snd) rfl
    simp only [f,centralParameterSlope,Complex.cos_zero,sub_self,familyMember]
    apply (analyticAt_const.mul hb).inv
    simpa [centralParameterSlope,familyMember] using
      centralParameterSlope_ne_zero (familyMember B eta) phi hphi 0 (by simpa [familyMember] using hB0 eta heta)
  obtain ⟨r,M,hr,hM,hbound⟩ := compact_analytic_uniform_bound f hQ hfa
  refine ⟨1/M,by positivity,?_⟩
  intro eta heta
  have hb := (hbound eta heta 0 (by simpa using hr)).2.le
  have hn : 0<‖centralParameterSlope (familyMember B eta) phi 0‖ := norm_pos_iff.mpr
    (centralParameterSlope_ne_zero (familyMember B eta) phi hphi 0 (by simpa [familyMember] using hB0 eta heta))
  change ‖(centralParameterSlope (familyMember B eta) phi 0)⁻¹‖≤M at hb
  rw [norm_inv] at hb
  rw [inv_eq_one_div] at hb
  have hh := (div_le_iff₀ hn).mp hb
  exact (div_le_iff₀ hM).mpr (by nlinarith)

theorem compact_family_pole_derivative_lower (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta)) (hB0 : ∀eta∈Q,B (0,eta)≠0) :
    ∃r c : ℝ,0<r ∧ 0<c ∧ ∀eta∈Q,∀N : ℕ,N≠0 → ∀d t : ℂ,∀v : Config N,
      ‖t‖<r → (∀i,‖d+v i‖<r) →
      c*N≤‖poleParameterDerivative (familyMember B eta) phi hphi d t v‖ := by
  obtain ⟨r,hr,hs⟩ := compact_family_uniform_slope B phi hphi hQ hB hB0
  obtain ⟨c,hc,hcl⟩ := compact_family_central_slope_lower B phi hphi hQ hB hB0
  refine ⟨r,c/2,hr,half_pos hc,?_⟩
  intro eta heta N hN d t v ht hv
  let c0 := centralParameterSlope (familyMember B eta) phi 0
  have ha i := (hs eta heta t (d+v i) ht (hv i)).1
  have hb i := (hs eta heta t (d+v i) ht (hv i)).2
  let a := mean (fun i=>phaseParameterSlope (familyMember B eta) phi hphi (t,d+v i))
  have he : ‖a-c0‖≤‖c0‖/4 := norm_mean_sub_le hN _ c0 (by positivity) hb
  have hal : c/2≤‖a‖ := by
    have hh := norm_sub_norm_le c0 a
    rw [norm_sub_rev] at hh
    change ‖c0‖-‖a‖≤‖a-c0‖ at hh
    have hl := hcl eta heta
    change c≤‖c0‖ at hl
    linarith [norm_nonneg c0]
  have hn : (N:ℂ)≠0 := by exact_mod_cast hN
  have hh := (poleAverage_hasDerivAt (familyMember B eta) phi hphi d t v ha).mul_const (N:ℂ)
  have hfun : (fun u=>poleAverage (familyMember B eta) phi hphi d u v*(N:ℂ))=
      (fun u=>poleEquation (familyMember B eta) phi hphi d u v) := by
    funext u
    exact div_mul_cancel₀ _ hn
  rw [hfun] at hh
  unfold poleParameterDerivative
  rw [hh.deriv,norm_mul,Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right hal (Nat.cast_nonneg N)

end
end IsingBulk.Joint.Negative
