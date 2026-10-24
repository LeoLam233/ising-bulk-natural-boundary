import IsingBulk.Anisotropic.NegativeNormalForm.DensityResiduePrefactor
import IsingBulk.Anisotropic.NegativeNormalForm.DensityResiduePair
import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueAverage

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeDominance
open scoped BigOperators

theorem densityPrefactor_ratio (B rootB : ℂ → ℂ) (n : ℕ) (t t₀ : ℂ) :
    densityPrefactor B rootB n t/densityPrefactor B rootB n t₀=
      (rootB t/rootB t₀)*(B t/B t₀)^alpha n := by
  have hc : (n.factorial:ℂ)*(2*(Real.pi:ℂ))^(n-1)≠0 := by
    apply mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n)
    apply pow_ne_zero
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  simp only [densityPrefactor]
  rw [div_div_div_cancel_right₀ hc,div_pow,mul_div_mul_comm]

theorem residuePairRatio_eq (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (t d x y : ℂ) :
    (halfSineSlope (x-y)/pairDenominator B phi hphi d t x y)^2/
      ((1/2)/((Real.sin phi:ℂ)*Complex.I))^2=residuePairRatio B phi hphi t d x y := by
  rw [←div_pow]
  simp only [residuePairRatio,residuePairDenominatorRatio,div_eq_mul_inv,mul_inv_rev,inv_inv,one_mul]
  ring

/-- Exact original numerator ratio as scalar factors, with no square-root
replacement and no omission of regular pair denominators. -/
theorem regularNumerator_ratio (B rootB : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    {n : ℕ} (t d : ℂ) (v : Config n) :
    regularNumerator B rootB phi hphi d t v/
        regularNumerator B rootB phi hphi d (1-Complex.cos d) (0:Config n)=
      (rootB t/rootB (1-Complex.cos d))*(B t/B (1-Complex.cos d))^alpha n *
        (∏i,residueOneBodyRatio B phi hphi (t,(d,v i))) *
        ∏p∈firstStrictPairs n,residuePairRatio B phi hphi t d (v p.1) (v p.2) := by
  let c : ℂ := (Real.sin phi:ℂ)*Complex.I
  have hcenter : regularNumerator B rootB phi hphi d (1-Complex.cos d) (0:Config n)=
      densityPrefactor B rootB n (1-Complex.cos d)*(∏_i:Fin n,c⁻¹)*
        ∏_p∈firstStrictPairs n,((1/2)/c)^2 := by
    rw [regularNumerator_center]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,firstStrictPairs_card,pow_mul]
    rfl
  rw [hcenter,regularNumerator,←div_mul_div_comm,←div_mul_div_comm,densityPrefactor_ratio]
  congr 1
  · congr 1
    rw [←Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [residueOneBodyRatio,div_eq_mul_inv,inv_inv]
    ring
  · rw [←Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p _
    exact residuePairRatio_eq B phi hphi t d (v p.1) (v p.2)

/-- Exact normalized residue, including the original phase derivative Γ_t. -/
theorem regularResidue_ratio_factorization {n : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d : ℂ) (T : Config n→ℂ)
    (hT : T 0=1-Complex.cos d) (hB : AnalyticAt ℂ B (1-Complex.cos d)) (v : Config n) :
    regularResidue B rootB phi hphi d T v/regularResidue B rootB phi hphi d T 0=
      ((rootB (T v)/rootB (1-Complex.cos d))*(B (T v)/B (1-Complex.cos d))^alpha n *
        (∏i,residueOneBodyRatio B phi hphi (T v,(d,v i))) *
        ∏p∈firstStrictPairs n,residuePairRatio B phi hphi (T v) d (v p.1) (v p.2)) *
      (((n:ℂ)*centralParameterSlope B phi d)/poleParameterDerivative B phi hphi d (T v) v) := by
  have hd : poleParameterDerivative B phi hphi d (1-Complex.cos d) (0:Config n)=
      (n:ℂ)*centralParameterSlope B phi d :=
    (poleEquation_hasDerivAt_center B phi hphi d _ hB.differentiableAt.hasDerivAt).deriv
  rw [←regularNumerator_ratio B rootB phi hphi (T v) d v]
  simp only [regularResidue,hT,hd,div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
