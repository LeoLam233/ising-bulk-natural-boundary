import IsingBulk.Anisotropic.NegativeNormalForm.FullDensityDomain
import IsingBulk.Anisotropic.NegativeNormalForm.VandermondeDensityError

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section

theorem normalizedFullDensity_factorization {m : ℕ} (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d : ℂ) (T : Config (m+1) → ℂ)
    (Phi : Config (m+1) → Config (m+1)) (u : Config m) :
    normalizedFullDensity B rootB phi hphi d T Phi u=
      (regularResidue B rootB phi hphi d T (Phi (freeChartCLM m u))/regularResidue B rootB phi hphi d T 0)*
        actualPairMultiplier Phi (freeChartCLM m u)^2*constrainedJacobian Phi u := by
  unfold normalizedFullDensity fullTransformedDensity
  ring

 theorem three_factor_exponential_error (a b c : ℂ) (A B C : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C)
    (ha : ‖a‖≤Real.exp A) (hb : ‖b‖≤Real.exp B) (hc : ‖c‖≤Real.exp C)
    (hea : ‖a-1‖≤A*Real.exp A) (heb : ‖b-1‖≤B*Real.exp B) (hec : ‖c-1‖≤C*Real.exp C) :
    ‖a*b*c‖≤Real.exp (A+B+C) ∧ ‖a*b*c-1‖≤(A+B+C)*Real.exp (A+B+C) := by
  have hexp : Real.exp (A+B+C)=Real.exp A*Real.exp B*Real.exp C := by rw [Real.exp_add,Real.exp_add]
  have heA : 1≤Real.exp A := Real.one_le_exp_iff.mpr hA
  have heB : 1≤Real.exp B := Real.one_le_exp_iff.mpr hB
  constructor
  · rw [norm_mul,norm_mul,hexp]
    exact mul_le_mul (mul_le_mul ha hb (norm_nonneg _) (Real.exp_pos A).le) hc
      (norm_nonneg _) (mul_nonneg (Real.exp_pos A).le (Real.exp_pos B).le)
  · have he : a*b*c-1=(a-1)*b*c+(b-1)*c+(c-1) := by ring
    rw [he]
    have ht := (norm_add_le ((a-1)*b*c+(b-1)*c) (c-1)).trans
      (add_le_add_left (norm_add_le ((a-1)*b*c) ((b-1)*c)) _)
    simp only [norm_mul] at ht
    have h1 : ‖a-1‖*‖b‖*‖c‖≤A*Real.exp (A+B+C) := by
      rw [hexp]
      calc
        _ ≤ (A*Real.exp A)*Real.exp B*Real.exp C := by gcongr
        _ = _ := by ring
    have h2 : ‖b-1‖*‖c‖≤B*Real.exp (A+B+C) := by
      have h := mul_le_mul heb hc (norm_nonneg _) (mul_nonneg hB (Real.exp_pos B).le)
      have hh := mul_le_mul_of_nonneg_right heA (show 0≤B*Real.exp B*Real.exp C by positivity)
      rw [hexp]
      nlinarith
    have h3 : ‖c-1‖≤C*Real.exp (A+B+C) := by
      have hh : Real.exp C≤Real.exp (A+B+C) := Real.exp_le_exp.mpr (by linarith)
      exact hec.trans (mul_le_mul_of_nonneg_left hh hC)
    nlinarith

end
end IsingBulk.Anisotropic.NegativeNormalForm
