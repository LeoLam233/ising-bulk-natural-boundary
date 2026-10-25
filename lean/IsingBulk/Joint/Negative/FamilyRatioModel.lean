import IsingBulk.Joint.Negative.FamilyActualRatio

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric FormFactors IsingBulk.Anisotropic.NegativeNormalForm
open MeasureTheory IsingBulk.First IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles
open scoped Topology

/-- Actual complex-ratio families satisfy the complete central Gamma-beta
model estimate with common constants, common cutoff and common particle threshold.
The model uses the actual B(tau N,lambda), not the central value. -/
theorem negative_ratio_normalized_model_error {edge amp : Coupling→ℂ} {z₀ lam₀ : ℂ}
    (F : ComplexRatioFamily edge amp (-1) z₀ lam₀) (phi : ℝ) (hphi : Real.sin phi≠0) :
    ∃delta R r Cp A : ℝ, 0<delta ∧ 0<R ∧ 0<r ∧ 0<Cp ∧ 0<A ∧
      delta≤R/4 ∧ 4*R≤r ∧
      ∀ b : ContDiffBump (0:ℝ), b.rOut<delta^2 →
      ∃Ct : ℝ,0<Ct ∧ ∀ᶠ m : ℕ in atTop, ∀eta∈closedBall lam₀ F.radius, Odd (m+1) →
      let d : ℂ := ((Real.pi/(m+1:ℕ):ℝ):ℂ)
      let H := centralHessian (familyMember F.anisotropy eta) phi d
      let c := H/((2*(m+1:ℕ):ℝ):ℂ)
      ∃ P : UniformProjectedWitness (familyMember F.anisotropy eta) phi hphi (m+1) d r Cp,
      ∃ J : UniformCorrectionWitness (familyMember F.anisotropy eta) phi hphi (m+1) d r Cp P R,
      regularResidue (familyMember F.anisotropy eta) (familyMember (NegativeRatioFamily.rootAnisotropy F) eta) phi hphi d P.T 0≠0 ∧
      ∀j : ℕ,8*(m+1)^2≤j →
      let M := model (familyMember F.anisotropy eta (tau (m+1))) (familyMember (NegativeRatioFamily.rootAnisotropy F) eta (tau (m+1))) H (Real.sin phi) (m+1) j
      let cut := ∫q : Fin m→ℝ,(shapeSpatialCutoff b q:ℂ)*quadraticModelKernel m j (tau (m+1)) c q
      let error := ∫q : Fin m→ℝ,(shapeSpatialCutoff b q:ℂ)*
        (normalizedFullDensity (familyMember F.anisotropy eta) (familyMember (NegativeRatioFamily.rootAnisotropy F) eta) phi hphi d P.T (fun y=>P.V (J.W y)) (complexify m q)-1)*
        quadraticModelKernel m j (tau (m+1)) c q
      ‖2*(regularResidue (familyMember F.anisotropy eta) (familyMember (NegativeRatioFamily.rootAnisotropy F) eta) phi hphi d P.T 0*(cut+error))-M‖≤
        (A*((m+1:ℕ)/Real.sqrt j+(m+1:ℕ)^2/j+Real.exp (-(j:ℝ)*Real.log 2/8))+
          Ct*(1/2:ℝ)^j)*‖M‖ := by
  exact compact_family_normalized_model_error F.anisotropy (NegativeRatioFamily.rootAnisotropy F)
    phi hphi (isCompact_closedBall lam₀ F.radius)
    (fun _ hl=>F.central_anisotropy_analytic hl) (fun _ hl=>F.central_anisotropy_ne_zero hl)
    (fun _ hl=>NegativeRatioFamily.rootAnisotropy_central_analytic F hl)
    (fun _ hl=>NegativeRatioFamily.rootAnisotropy_central_ne_zero F hl)
    ⟨1,zero_lt_one,fun _ _ _ _=>NegativeRatioFamily.rootAnisotropy_sq F _⟩

end
end IsingBulk.Joint.Negative
