import IsingBulk.Joint.Negative.FamilyCentralGaussian
import IsingBulk.Anisotropic.NegativeNormalForm.ActualCentralFixedCutoff

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open Filter IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles
open scoped Topology

/-- The central estimate with a fixed physical cutoff and no auxiliary bump or
normal-form witness in its interface. The exact Hessian normalization is rewritten
to the physical model used by the complete coefficient range assembly. -/
theorem compact_family_central_fixed_cutoff (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈Q,B (0,eta)≠0)
    (hroot : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta)) (hrootn : ∀eta∈Q,rootB (0,eta)≠0)
    (hsq : ∃s : ℝ,0<s ∧ ∀eta∈Q,∀t : ℂ,‖t‖<s → rootB (t,eta)^2=B (t,eta)) :
    ∃sigma : ℝ,0<sigma ∧ ∀s : ℝ,0<s → s<sigma →
      ∃A g D : ℝ,0<A ∧ 0<g ∧ 0<D ∧
      ∀ᶠ m : ℕ in atTop, ∀eta∈Q, ∀j : ℕ,8*(2*m+1)^2≤j →
      ‖2*(iteratedDeriv j
          (centeredKernelIntegral (familyMember B eta) (familyMember rootB eta) phi hphi m (Real.pi/(2*m+1:ℕ)) s) 0/(j.factorial:ℂ))-
          physicalModel (familyMember B eta) (familyMember rootB eta) phi (2*m+1) j‖≤
        A*((2*m+1:ℕ)/Real.sqrt j+(2*m+1:ℕ)^2/j+Real.exp (-(j:ℝ)*Real.log 2/8))*
          ‖physicalModel (familyMember B eta) (familyMember rootB eta) phi (2*m+1) j‖+
        gaussianEnvelope g D (2*m+1) j := by
  obtain ⟨delta,sigma,hd,hsigma,hex⟩ :=
    compact_family_central_gaussian_error B rootB phi hphi hQ hB hBn hroot hrootn hsq
  refine ⟨sigma,hsigma,?_⟩
  intro s hs hss
  let t := min (delta^2) (s/2)
  have ht : 0<t := lt_min (sq_pos_of_pos hd) (by positivity)
  have htd : t≤delta^2 := min_le_left _ _
  have hts : t≤s/2 := min_le_right _ _
  let b : ContDiffBump (0:ℝ) := ⟨t/4,t/2,by positivity,by linarith⟩
  have hb : b.rOut<delta^2 := by change t/2<delta^2; linarith
  have hbs : b.rOut≤s/2 := by change t/2≤s/2; linarith
  obtain ⟨A,g,D,hA,hg,hD,hbound⟩ := hex b hb
  refine ⟨A,g,D,hA,hg,hD,?_⟩
  filter_upwards [hbound s hs hss hbs] with m hm eta heta
  have hm := hm eta heta
  intro j hj
  simpa only [physicalModel,centralHessian_at_winding,gaussianEnvelope] using hm j hj

end
end IsingBulk.Joint.Negative
