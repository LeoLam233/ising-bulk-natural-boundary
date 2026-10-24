import IsingBulk.Anisotropic.NegativeDominance.ResidueUniformBound
import IsingBulk.Anisotropic.NegativeDominance.ConstrainedBetaKernel

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.First
open scoped BigOperators

/-- The true real-pole energy supplies the exact positive beta denominator,
not just a constant lower bound for the pole. -/
theorem poleTaylorIntegrand_beta_uniform_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hrB : AnalyticAt ℂ rootB 0)
    (hB0 : B 0≠0) :
    ∃r M c : ℝ,0<r ∧ 1≤M ∧ 0<c ∧ ∀n : ℕ,∀d : ℝ,
      ∀T : Config (n+1)→ℂ,∀x : Fin n→ℝ,
      |d|<r → ‖T (complexShape x)‖<r → (∀i,|shapeExtend x i|<r) →
      poleEquation B phi hphi (d : ℂ) (T (complexShape x)) (complexShape x)=0 →
      0<1-Real.cos d → ∀j : ℕ,
      ‖poleTaylorIntegrand B rootB phi hphi (d : ℂ) T j (complexShape x)‖≤
        (2*M^(1+alpha (n+1)+(n+1)+(n+1).choose 2)/(c*(n+1)))*
        constrainedBetaKernel n j (1-Real.cos d) (1/(4*(n+1))) x := by
  obtain ⟨rR,M,c,hrR,hM,hc,hR⟩ := poleResidue_vandermonde_uniform_bound B rootB phi hphi hB hrB hB0
  obtain ⟨rE,hrE,hE⟩ := actual_pole_real_energy_lower B phi hphi hB hB0
  let r := min rR rE
  have hrR' : r≤rR := min_le_left _ _
  have hrE' : r≤rE := min_le_right _ _
  refine ⟨r,M,c,lt_min hrR hrE,hM,hc,?_⟩
  intro n d T x hd ht hv hpole hτ j
  have he := hE (n+1) (by omega) d (T (complexShape x)) (shapeExtend x)
    (hd.trans_le hrE') (ht.trans_le hrE') (fun i => (hv i).trans_le hrE')
    (complexShape_zeroMean x) hpole
  have hres := hR (n+1) (by omega) (d : ℂ) T (complexShape x)
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
end IsingBulk.Anisotropic.NegativeDominance
