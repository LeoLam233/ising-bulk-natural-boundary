import IsingBulk.Anisotropic.NegativeCycles.ComplexNumeratorBound
import IsingBulk.Anisotropic.NegativeCycles.ActualResidueSlope

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeNormalForm

/-- Gaussian residue bound on the actual complex neighborhood, not only on real angles. -/
theorem poleResidue_complex_uniform_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hroot : AnalyticAt ℂ rootB 0)
    (hBn : B 0≠0) :
    ∃r M c : ℝ,0<r ∧ 1≤M ∧ 0<c ∧ ∀m : ℕ, ∀d : ℂ,
      ∀T : Config (2*m+1)→ℂ, ∀v : Config (2*m+1),
      ‖d‖<r → ‖T v‖<r → (∀i, ‖v i‖<r) →
      ‖poleResidue B rootB phi hphi d T v‖≤
        2*((M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2))/(c*(2*m+1:ℕ)) := by
  obtain ⟨a,M,ha,hM,hnum⟩ := formFactorNumerator_complex_uniform_bound B rootB phi hphi hB hroot
  obtain ⟨b,c,hb,hc,hslope⟩ := poleParameterDerivative_uniform_lower B phi hphi hB hBn
  let r := min a (b/2)
  have hr : 0<r := lt_min ha (half_pos hb)
  have hra : r≤a := min_le_left _ _
  have hrb : r≤b/2 := min_le_right _ _
  refine ⟨r,M,c,hr,hM,hc,?_⟩
  intro m d T v hd ht hv
  have hN := hnum m d (T v) v (hd.trans_le hra) (ht.trans_le hra) (fun i => (hv i).trans_le hra)
  have hD := hslope (2*m+1) (by omega) d (T v) v (by linarith)
    (fun i => lt_of_le_of_lt (norm_add_le d (v i)) (by linarith [hv i]))
  unfold poleResidue
  rw [norm_div,norm_mul,norm_neg]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hN (by norm_num))
    (by positivity) hD

/-- All Taylor orders on a pole-free complex annulus inherit the Gaussian numerator. -/
theorem poleResidue_quotient_norm_le {N : ℕ} {R T : ℂ} {G c σ : ℝ}
    (hN : 0<N) (hc : 0<c) (hσ : 0<σ) (hG : 0≤G)
    (hR : ‖R‖≤2*G/(c*N)) (hT : σ/(8*N)≤‖T‖) (j : ℕ) :
    ‖R/T^(j+1)‖≤(2*G/(c*N))*((8*N:ℝ)/σ)^(j+1) := by
  have hnR : (0:ℝ)<N := by exact_mod_cast hN
  have hgap : 0<σ/(8*N) := by positivity
  have ht : 0<‖T‖ := hgap.trans_le hT
  rw [norm_div,norm_pow,div_eq_mul_inv]
  apply mul_le_mul hR _ (by positivity) (by positivity)
  rw [←inv_pow]
  apply pow_le_pow_left₀ (by positivity)
  calc
    ‖T‖⁻¹ ≤ (σ/(8*N))⁻¹ := inv_anti₀ hgap hT
    _ = (8*N:ℝ)/σ := by rw [inv_div]

end IsingBulk.Anisotropic.NegativeCycles
