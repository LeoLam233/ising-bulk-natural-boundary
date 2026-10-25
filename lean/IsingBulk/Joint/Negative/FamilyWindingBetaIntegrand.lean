import IsingBulk.Joint.Negative.FamilyWindingResidue
import IsingBulk.Joint.Negative.FamilyWindingEnergy
import IsingBulk.Anisotropic.NegativeDominance.PoleBetaIntegrand

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles IsingBulk.Anisotropic.NegativeDominance
open scoped BigOperators Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
/-- The true real-pole energy supplies the exact positive beta denominator,
not just a constant lower bound for the pole. -/
theorem compact_family_pole_beta_integrand_bound (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hrB : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta))
    (hB0 : ∀eta∈Q,B (0,eta)≠0) :
    ∃r M c : ℝ,0<r ∧ 1≤M ∧ 0<c ∧ ∀eta∈Q,∀n : ℕ,∀d : ℝ,
      ∀T : Config (n+1)→ℂ,∀x : Fin n→ℝ,
      |d|<r → ‖T (complexShape x)‖<r → (∀i,|shapeExtend x i|<r) →
      poleEquation (familyMember B eta) phi hphi (d : ℂ) (T (complexShape x)) (complexShape x)=0 →
      0<1-Real.cos d → ∀j : ℕ,
      ‖poleTaylorIntegrand (familyMember B eta) (familyMember rootB eta) phi hphi (d : ℂ) T j (complexShape x)‖≤
        (2*M^(1+alpha (n+1)+(n+1)+(n+1).choose 2)/(c*(n+1)))*
        constrainedBetaKernel n j (1-Real.cos d) (1/(4*(n+1))) x := by
  obtain ⟨rR,M,c,hrR,hM,hc,hR⟩ := compact_family_residue_vandermonde_bound B rootB phi hphi hQ hB hrB hB0
  obtain ⟨rE,hrE,hE⟩ := compact_family_real_pole_energy_lower B phi hphi hQ hB hB0
  let r := min rR rE
  have hrR' : r≤rR := min_le_left _ _
  have hrE' : r≤rE := min_le_right _ _
  refine ⟨r,M,c,lt_min hrR hrE,hM,hc,?_⟩
  intro eta heta n d T x hd ht hv hpole hτ j
  have he := hE eta heta (n+1) (by omega) d (T (complexShape x)) (shapeExtend x)
    (hd.trans_le hrE') (ht.trans_le hrE') (fun i => (hv i).trans_le hrE')
    (complexShape_zeroMean x) hpole
  have hres := hR eta heta (n+1) (by omega) (d : ℂ) T (complexShape x)
    (by simpa using hd.trans_le hrR') (ht.trans_le hrR')
    (fun i => by simpa [complexShape] using (hv i).trans_le hrR')
  have hden : 0<1-Real.cos d+(∑i : Fin (n+1),(shapeExtend x i)^2)/(4*(n+1 : ℝ)) := by positivity
  have hnorm : 1-Real.cos d+(∑i : Fin (n+1),(shapeExtend x i)^2)/(4*(n+1 : ℝ))≤‖T (complexShape x)‖ := by
    have hh := he.trans (Complex.re_le_norm _)
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hp := pow_le_pow_left₀ hden.le hnorm (j+1)
  unfold poleTaylorIntegrand
  rw [norm_div,norm_pow]
  have hb := div_le_div₀ (by positivity) hres (pow_pos hden _) hp
  rw [show ‖vandermonde (complexShape x)‖^2=firstVandermonde (shapeExtend x)^2 from
    norm_vandermonde_real_sq (shapeExtend x)] at hb
  convert hb using 1
  simp only [constrainedBetaKernel,Nat.cast_add,Nat.cast_one]
  ring

end
end IsingBulk.Joint.Negative
