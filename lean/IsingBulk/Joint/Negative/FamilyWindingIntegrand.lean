import IsingBulk.Joint.Negative.FamilyWindingEnergy
import IsingBulk.Joint.Negative.FamilyWindingNumerator
import IsingBulk.Joint.Negative.FamilyWindingSlope
import IsingBulk.Anisotropic.NegativeDominance.PoleCoefficientBound

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles IsingBulk.Anisotropic.NegativeDominance
open scoped BigOperators Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
/-- Uniform all-order bound for the actual pole coefficient integrand. The only
pole premise is its defining equation; no coefficient estimate is assumed. -/
theorem compact_family_pole_integrand_bound (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hrB : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta))
    (hB0 : ∀eta∈Q,B (0,eta)≠0) :
    ∃ r M c : ℝ,0<r ∧ 1≤M ∧ 0<c ∧ ∀eta∈Q,∀n : ℕ,n≠0 → ∀d : ℝ,
    ∀T : Config n→ℂ, ∀v : Fin n→ℝ,
      |d|<r → ‖T (fun i => (v i : ℂ))‖<r → (∀i,|v i|<r) →
      ZeroMean (fun i => (v i : ℂ)) →
      poleEquation (familyMember B eta) phi hphi (d : ℂ) (T (fun i => (v i : ℂ))) (fun i => (v i : ℂ))=0 →
      Real.pi/(n : ℝ)≤|d| → ∀j : ℕ,
      ‖poleTaylorIntegrand (familyMember B eta) (familyMember rootB eta) phi hphi (d : ℂ) T j (fun i => (v i : ℂ))‖≤
        ‖vandermonde (fun i => (v i : ℂ))‖^2 *
        (2*M^(1+alpha n+n+n.choose 2)/(c*n))*((n : ℝ)^2/2)^(j+1) := by
  obtain ⟨rE,hrE,hE⟩ := compact_family_real_pole_energy_lower B phi hphi hQ hB hB0
  obtain ⟨rF,M,hrF,hM,hF⟩ := compact_family_numerator_vandermonde_bound B rootB phi hphi hQ hB hrB
  obtain ⟨rS,c,hrS,hc,hS⟩ := compact_family_pole_derivative_lower B phi hphi hQ hB hB0
  let r := min rE (min rF (min (rS/2) Real.pi))
  have hr : 0<r := lt_min hrE (lt_min hrF (lt_min (by positivity) Real.pi_pos))
  have hrE' : r≤rE := min_le_left _ _
  have hrF' : r≤rF := (min_le_right _ _).trans (min_le_left _ _)
  have hrS' : r≤rS/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrpi : r≤Real.pi := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨r,M,c,hr,hM,hc,?_⟩
  intro eta heta n hn d T v hd ht hv hmean hpole hwind j
  let vc : Config n := fun i => (v i : ℂ)
  have hnR : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hgap : 2/(n : ℝ)^2≤‖T vc‖ := by
    have he := hE eta heta n hn d (T vc) v (hd.trans_le hrE') (ht.trans_le hrE')
      (fun i => (hv i).trans_le hrE') hmean hpole
    have htau := one_sub_cos_winding_lower n hn d (hd.le.trans hrpi) hwind
    have hq : 0≤(∑i,(v i)^2)/(4*(n : ℝ)) := by positivity
    exact (show 2/(n : ℝ)^2≤(T vc).re by linarith).trans (Complex.re_le_norm _)
  have hnum := hF eta heta n (d : ℂ) (T vc) vc (by simpa using hd.trans_le hrF')
    (ht.trans_le hrF') (fun i => by simpa [vc] using (hv i).trans_le hrF')
  have hslope : c*n≤‖poleParameterDerivative (familyMember B eta) phi hphi (d : ℂ) (T vc) vc‖ := by
    apply hS eta heta n hn (d : ℂ) (T vc) vc (by linarith)
    intro i
    calc
      ‖(d : ℂ)+vc i‖ ≤ ‖(d : ℂ)‖+‖vc i‖ := norm_add_le _ _
      _ = |d|+|v i| := by simp [vc]
      _ < rS := by linarith [hv i]
  have hden : 0<c*(n : ℝ) := mul_pos hc hnR
  have hres : ‖poleResidue (familyMember B eta) (familyMember rootB eta) phi hphi (d : ℂ) T vc‖≤
      2*(‖vandermonde vc‖^2*M^(1+alpha n+n+n.choose 2))/(c*n) := by
    norm_num only [poleResidue,norm_div,norm_mul,norm_neg,Complex.norm_ofNat]
    exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnum (by norm_num)) hden hslope
  have hpow : (2/(n : ℝ)^2)^(j+1)≤‖T vc‖^(j+1) :=
    pow_le_pow_left₀ (by positivity) hgap _
  change ‖poleResidue (familyMember B eta) (familyMember rootB eta) phi hphi (d : ℂ) T vc/(T vc)^(j+1)‖≤_
  rw [norm_div,norm_pow]
  calc
    _ ≤ (2*(‖vandermonde vc‖^2*M^(1+alpha n+n+n.choose 2))/(c*n))/(2/(n : ℝ)^2)^(j+1) :=
      div_le_div₀ (by positivity) hres (by positivity) hpow
    _ = _ := by simp only [div_pow]; dsimp only [vc]; field_simp

end
end IsingBulk.Joint.Negative
