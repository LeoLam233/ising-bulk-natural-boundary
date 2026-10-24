import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueActual

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section

/-- The requested relative O(sqrt(n q)+n q) estimate on the small-energy
region, derived from the global exponential envelope for the actual residue. -/
theorem exists_actual_regularResidue_small_energy_error (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0)
    (hroot : AnalyticAt ℂ rootB 0) (hrootn : rootB 0≠0)
    (r C R D : ℝ) (hr : 0<r) (hC : 0<C) (hR : 0<R) (hRr : R≤r/2) (hD : 0≤D) :
    ∃ δ K : ℝ, 0<δ ∧ 0<K ∧ δ≤R/4 ∧ ∀ n : ℕ, n≠0 → ∀ d : ℂ,
      ‖d‖<δ → (n:ℝ)*‖d‖≤D →
      ∀ P : UniformProjectedWitness B phi hphi n d r C,
      ∀ J : UniformCorrectionWitness B phi hphi n d r C P R,
      ∀ y : Config n, ‖y‖<δ → ZeroMean y → (n:ℝ)*absoluteEnergy y≤1/4 →
      ‖regularResidue B rootB phi hphi d P.T (P.V (J.W y))/
          regularResidue B rootB phi hphi d P.T 0-1‖≤
        K*(Real.sqrt ((n:ℝ)*absoluteEnergy y)+(n:ℝ)*absoluteEnergy y) := by
  obtain ⟨δ,K,hδ,hK,hδR,hactual⟩ := exists_actual_regularResidue_error B rootB phi hphi hB hBn
    hroot hrootn r C R D hr hC hR hRr hD
  refine ⟨δ,K*Real.exp K,hδ,mul_pos hK (Real.exp_pos K),hδR,?_⟩
  intro n hn d hd hdD P J y hy hmy hsmall
  have hh := (hactual n hn d hd hdD P J y hy hmy).2
  let q := (n:ℝ)*absoluteEnergy y
  have hq : 0≤q := mul_nonneg (Nat.cast_nonneg n) (absoluteEnergy_nonneg y)
  have hs : 0≤Real.sqrt q := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt hq
  have he : Real.sqrt q+q≤1 := by change q≤1/4 at hsmall; nlinarith
  have hle : K*(Real.sqrt q+q)≤K := by nlinarith
  have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle)
    (show 0≤K*(Real.sqrt q+q) by positivity)
  apply hh.trans
  convert h using 1; ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
