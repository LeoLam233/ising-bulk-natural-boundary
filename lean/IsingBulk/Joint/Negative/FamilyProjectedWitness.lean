import IsingBulk.Joint.Negative.FamilyProjectedInverse
import IsingBulk.Anisotropic.NegativeNormalForm.UniformProjectedWitness
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
 theorem compact_family_projected_witness (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {P : Set E} (hP : IsCompact P)
    (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta)) (hB0 : ∀eta∈P,B (0,eta)≠0) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀eta∈P,∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<r →
      Nonempty (UniformProjectedWitness (familyMember B eta) phi hphi n d r C) := by
  obtain ⟨r,C,hr,hC,hex⟩ := compact_family_projected_inverse B phi hphi hP hB hB0
  refine ⟨r,C,hr,hC,?_⟩
  intro eta heta n hn d hd
  obtain ⟨T,V,hT,hT0,hTp,hTs,hTL,hFL,hVa,hV,hV0,hdV,hVp,hVs,hVL⟩ := hex eta heta n hn d hd
  exact ⟨⟨T,V,hT,hT0,hTp,hTs,hTL,hFL,hVa,hV,hV0,hdV,hVp,hVs,hVL⟩⟩

end
end IsingBulk.Joint.Negative
