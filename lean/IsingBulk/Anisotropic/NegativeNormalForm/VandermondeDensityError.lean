import IsingBulk.Anisotropic.NegativeNormalForm.UniformVandermondeLog

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section

 theorem complex_exp_error_envelope (z : ℂ) (A : ℝ) (hz : ‖z‖≤A) :
    ‖Complex.exp z-1‖≤2*A*Real.exp A := by
  have hA : 0≤A := (norm_nonneg z).trans hz
  have heA : 1≤Real.exp A := Real.one_le_exp_iff.mpr hA
  by_cases hsmall : A≤1
  · have h := (Complex.norm_exp_sub_one_le (hz.trans hsmall)).trans (mul_le_mul_of_nonneg_left hz (by norm_num))
    exact h.trans (le_mul_of_one_le_right (by positivity) heA)
  · have hlarge : 1<A := lt_of_not_ge hsmall
    have h := norm_sub_le (Complex.exp z) (1:ℂ)
    rw [norm_one] at h
    have he := (Complex.norm_exp_le_exp_norm z).trans (Real.exp_le_exp.mpr hz)
    have hm := mul_le_mul_of_nonneg_right hlarge.le (Real.exp_pos A).le
    nlinarith

/-- Uniform actual inverse Vandermonde density and its complex error. -/
theorem exists_uniform_vandermonde_density_error (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) (D : ℝ) (hD : 0≤D) :
    ∃ δ R r Cp K : ℝ, 0<δ ∧ 0<R ∧ 0<r ∧ 0<Cp ∧ 0<K ∧ δ≤R/2 ∧ 4*R≤r ∧
      ∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ → (n:ℝ)*‖d‖≤D →
      ∃ P : UniformProjectedWitness B phi hphi n d r Cp,
      ∃ J : UniformCorrectionWitness B phi hphi n d r Cp P R,
      ∀ y : Config n, ‖y‖<δ → ZeroMean y →
      let E := Real.sqrt ((n:ℝ)*absoluteEnergy y)+(n:ℝ)*absoluteEnergy y
      ‖actualPairMultiplier (fun z => P.V (J.W z)) y^2‖≤Real.exp (K*E) ∧
      ‖actualPairMultiplier (fun z => P.V (J.W z)) y^2-1‖≤K*E*Real.exp (K*E) := by
  obtain ⟨δ,R,r,Cp,K,hδ,hR,hr,hCp,hK,hδR,hRr,hex⟩ :=
    exists_uniform_vandermonde_log B phi hphi hB hBn D hD
  refine ⟨δ,R,r,Cp,2*K,hδ,hR,hr,hCp,by positivity,hδR,hRr,?_⟩
  intro n hn d hd hdD
  obtain ⟨P,J,hlog⟩ := hex n hn d hd hdD
  refine ⟨P,J,?_⟩
  intro y hy hmy
  obtain ⟨he,hl⟩ := hlog y hy hmy
  dsimp only
  let E := Real.sqrt ((n:ℝ)*absoluteEnergy y)+(n:ℝ)*absoluteEnergy y
  have hE : 0≤E := add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Nat.cast_nonneg n) (absoluteEnergy_nonneg y))
  have hKE : K*E≤2*K*E := by nlinarith
  constructor
  · rw [← he]
    exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (hl.trans hKE))
  · rw [← he]
    have h := complex_exp_error_envelope _ (K*E) hl
    have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hKE) (show 0≤2*K*E by positivity)
    exact h.trans (by convert hm using 1; ring)

end
end IsingBulk.Anisotropic.NegativeNormalForm
