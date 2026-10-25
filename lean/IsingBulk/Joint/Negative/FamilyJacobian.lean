import IsingBulk.Joint.Negative.FamilyCorrectionInverse
import IsingBulk.Anisotropic.NegativeNormalForm.FullDensityEnvelope

/-! The actual constrained Jacobian, uniformly over a compact complex family.
All constants precede both the family member and the particle number. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_family_constrainedJacobian_log_bound (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta) ≠ 0) :
    ∃ R r C : ℝ, 0 < R ∧ 0 < r ∧ 0 < C ∧ 4*R ≤ r ∧
      ∀ eta ∈ K, ∀ m : ℕ, ∀ d : ℂ, ‖d‖ < R →
      ∃ P : UniformProjectedWitness (familyMember B eta) phi hphi (m+1) d r C,
      ∃ J : UniformCorrectionWitness (familyMember B eta) phi hphi (m+1) d r C P R,
      ∀ u : Config m, ‖freeChartCLM m u‖ ≤ R/4 →
      ∃ ell : ℂ, Complex.exp ell = constrainedJacobian (fun y => P.V (J.W y)) u ∧
        ‖ell‖ ≤ 4*(m+1:ℕ)*(‖freeChartCLM m u‖/(R/2))^2 := by
  obtain ⟨R,r,C,hR,hr,hC,hRr,hw⟩ := compact_family_correction_witness B phi hphi hK hB hB0
  refine ⟨R,r,C,hR,hr,hC,hRr,?_⟩
  intro eta heta m d hd
  obtain ⟨P,⟨J⟩⟩ := hw eta heta (m+1) (by omega) d hd
  exact ⟨P,J,fun u hu => J.constrainedJacobian_log_bound (familyMember B eta) phi hphi d r C R P
    hr hR (by linarith) u hu⟩

theorem compact_family_constrainedJacobian_energy_envelope (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hB0 : ∀ eta ∈ K, B (0,eta) ≠ 0) :
    ∃ R r C L : ℝ, 0 < R ∧ 0 < r ∧ 0 < C ∧ 0 < L ∧ 4*R ≤ r ∧
      ∀ eta ∈ K, ∀ m : ℕ, ∀ d : ℂ, ‖d‖ < R →
      ∃ P : UniformProjectedWitness (familyMember B eta) phi hphi (m+1) d r C,
      ∃ J : UniformCorrectionWitness (familyMember B eta) phi hphi (m+1) d r C P R,
      ∀ u : Config m, ‖freeChartCLM m u‖ ≤ R/4 →
      let H := Real.sqrt ((m+1:ℕ)*absoluteEnergy (freeChartCLM m u))+
        (m+1:ℕ)*absoluteEnergy (freeChartCLM m u)
      ‖constrainedJacobian (fun y => P.V (J.W y)) u‖ ≤ Real.exp (L*H) ∧
      ‖constrainedJacobian (fun y => P.V (J.W y)) u-1‖ ≤ L*H*Real.exp (L*H) := by
  obtain ⟨R,r,C,hR,hr,hC,hRr,hw⟩ := compact_family_correction_witness B phi hphi hK hB hB0
  refine ⟨R,r,C,8/(R/2)^2,hR,hr,hC,by positivity,hRr,?_⟩
  intro eta heta m d hd
  obtain ⟨P,⟨J⟩⟩ := hw eta heta (m+1) (by omega) d hd
  exact ⟨P,J,fun u hu => J.constrainedJacobian_energy_envelope (familyMember B eta) phi hphi d r C R P
    hr hR (by linarith) u hu⟩

end
end IsingBulk.Joint.Negative
