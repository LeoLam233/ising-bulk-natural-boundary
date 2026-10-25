import IsingBulk.Joint.Negative.FamilyCentralWinding
import IsingBulk.Anisotropic.NegativeNormalForm.ActualCentralGaussian

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open Filter IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles
open scoped Topology

/-- The actual central winding coefficient has the exact model, a vanishing
relative density error, and one sharp Gaussian analytic error. The conclusion
contains no normal-form witnesses, residue hypotheses, or abstract envelopes. -/
theorem compact_family_central_gaussian_error (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈Q,B (0,eta)≠0)
    (hroot : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta)) (hrootn : ∀eta∈Q,rootB (0,eta)≠0)
    (hsq : ∃s : ℝ,0<s ∧ ∀eta∈Q,∀t : ℂ,‖t‖<s → rootB (t,eta)^2=B (t,eta)) :
    ∃delta sigma : ℝ,0<delta ∧ 0<sigma ∧
      ∀b : ContDiffBump (0:ℝ),b.rOut<delta^2 →
      ∃A g D : ℝ,0<A ∧ 0<g ∧ 0<D ∧
      ∀s : ℝ,0<s → s<sigma → b.rOut≤s/2 →
      ∀ᶠ m : ℕ in atTop, ∀eta∈Q, ∀j : ℕ,8*(2*m+1)^2≤j →
      let N := 2*m+1
      let d : ℝ := Real.pi/(N:ℝ)
      let M := model (familyMember B eta (tau N)) (familyMember rootB eta (tau N)) (centralHessian (familyMember B eta) phi (d:ℂ)) (Real.sin phi) N j
      ‖2*(iteratedDeriv j (centeredKernelIntegral (familyMember B eta) (familyMember rootB eta) phi hphi m d s) 0/(j.factorial:ℂ))-M‖≤
        A*((N:ℝ)/Real.sqrt j+(N:ℝ)^2/j+Real.exp (-(j:ℝ)*Real.log 2/8))*‖M‖+
        Real.exp (-g*(N:ℝ)^2+((j:ℝ)+1)*Real.log N+D*((j:ℝ)+1)) := by
  obtain ⟨delta,sigma,cR,KR,MR,Ma,ca,La,rc,Mc,cc,Lc,hd,hsigma,hcR,hKR,hMR,hMa,hca,hLa,
    hrc,hMc,hcc,hLc,hex⟩ :=
    compact_family_central_winding_model_error B rootB phi hphi hQ hB hBn hroot hrootn hsq
  refine ⟨delta,sigma,hd,hsigma,?_⟩
  intro b hb
  obtain ⟨A,K,hA,hK,hex⟩ := hex b hb
  obtain ⟨g,D,hg,hD,hgauss⟩ := central_analytic_errors_gaussian_bound
    sigma cR KR MR Ma ca La rc Mc cc Lc K b.rIn hsigma hcR hKR hMR hMa hca hLa hrc hMc hcc hLc hK.le b.rIn_pos
  refine ⟨A,g,D,hA,hg,hD,?_⟩
  intro s hs hss hbs
  filter_upwards [hex s hs hss hbs,eventually_ge_atTop (1:ℕ)] with m hm hmpos eta heta
  have hm := hm eta heta
  intro j hj
  dsimp only
  exact (hm j hj).trans (add_le_add (le_refl _) (hgauss m (by omega) j (Real.pi/(2*m+1:ℕ)) s hss.le))

end
end IsingBulk.Joint.Negative
