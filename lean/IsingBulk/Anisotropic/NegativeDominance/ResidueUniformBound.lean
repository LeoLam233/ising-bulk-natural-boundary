import IsingBulk.Anisotropic.NegativeDominance.PoleCoefficientBound

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.Anisotropic.NegativeCycles

/-- Full actual residues retain a Vandermonde square on one complex
neighborhood, with every constant before the particle number. -/
theorem poleResidue_vandermonde_uniform_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hrB : AnalyticAt ℂ rootB 0)
    (hB0 : B 0≠0) :
    ∃r M c : ℝ,0<r ∧ 1≤M ∧ 0<c ∧ ∀n : ℕ,n≠0 → ∀d : ℂ,
      ∀T : Config n→ℂ,∀v : Config n,
      ‖d‖<r → ‖T v‖<r → (∀i,‖v i‖<r) →
      ‖poleResidue B rootB phi hphi d T v‖≤
        ‖vandermonde v‖^2*(2*M^(1+alpha n+n+n.choose 2)/(c*n)) := by
  obtain ⟨rF,M,hrF,hM,hF⟩ := formFactorNumerator_vandermonde_uniform_bound B rootB phi hphi hB hrB
  obtain ⟨rS,c,hrS,hc,hS⟩ := poleParameterDerivative_uniform_lower B phi hphi hB hB0
  let r := min rF (rS/2)
  have hr : 0<r := lt_min hrF (by positivity)
  have hrF' : r≤rF := min_le_left _ _
  have hrS' : r≤rS/2 := min_le_right _ _
  refine ⟨r,M,c,hr,hM,hc,?_⟩
  intro n hn d T v hd ht hv
  have hnR : (0 : ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnum := hF n d (T v) v (hd.trans_le hrF') (ht.trans_le hrF')
    (fun i => (hv i).trans_le hrF')
  have hslope : c*n≤‖poleParameterDerivative B phi hphi d (T v) v‖ := by
    apply hS n hn d (T v) v (by linarith)
    intro i
    exact (norm_add_le _ _).trans_lt (by linarith [hv i])
  norm_num only [poleResidue,norm_div,norm_mul,norm_neg,Complex.norm_ofNat]
  calc
    _ ≤ 2*(‖vandermonde v‖^2*M^(1+alpha n+n+n.choose 2))/(c*n) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hnum (by norm_num))
        (mul_pos hc hnR) hslope
    _ = _ := by ring

end
end IsingBulk.Anisotropic.NegativeDominance
