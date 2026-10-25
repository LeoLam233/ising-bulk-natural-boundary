import IsingBulk.Joint.Negative.FamilyVandermonde
import IsingBulk.Anisotropic.NegativeNormalForm.VandermondeDensityError

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
/-- Uniform actual inverse Vandermonde density and its complex error. -/
theorem compact_family_vandermonde_density_error (B : ℂ × E→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    {P : Set E} (hP : IsCompact P) (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈P,B (0,eta)≠0) (D : ℝ) (hD : 0≤D) :
    ∃ δ R r Cp K : ℝ, 0<δ ∧ 0<R ∧ 0<r ∧ 0<Cp ∧ 0<K ∧ δ≤R/2 ∧ 4*R≤r ∧
      ∀eta∈P,∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ → (n:ℝ)*‖d‖≤D →
      ∃ P : UniformProjectedWitness (familyMember B eta) phi hphi n d r Cp,
      ∃ J : UniformCorrectionWitness (familyMember B eta) phi hphi n d r Cp P R,
      ∀ y : Config n, ‖y‖<δ → ZeroMean y →
      let E := Real.sqrt ((n:ℝ)*absoluteEnergy y)+(n:ℝ)*absoluteEnergy y
      ‖actualPairMultiplier (fun z => P.V (J.W z)) y^2‖≤Real.exp (K*E) ∧
      ‖actualPairMultiplier (fun z => P.V (J.W z)) y^2-1‖≤K*E*Real.exp (K*E) := by
  obtain ⟨δ,R,r,Cp,K,hδ,hR,hr,hCp,hK,hδR,hRr,hex⟩ :=
    compact_family_vandermonde_log B phi hphi hP hB hBn D hD
  refine ⟨δ,R,r,Cp,2*K,hδ,hR,hr,hCp,by positivity,hδR,hRr,?_⟩
  intro eta heta n hn d hd hdD
  obtain ⟨P,J,hlog⟩ := hex eta heta n hn d hd hdD
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
end IsingBulk.Joint.Negative
