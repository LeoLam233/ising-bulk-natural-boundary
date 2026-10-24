import IsingBulk.Anisotropic.NegativeNormalForm.ActualCentralGaussian
import IsingBulk.Anisotropic.NegativeDominance.GaussianEnvelopeAlgebra
import IsingBulk.Anisotropic.NegativeDominance.PhysicalConcavity

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Filter IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeCycles
open scoped Topology

/-- The central estimate with a fixed physical cutoff and no auxiliary bump or
normal-form witness in its interface. The exact Hessian normalization is rewritten
to the physical model used by the complete coefficient range assembly. -/
theorem exists_actual_central_fixed_cutoff (B rootB : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) (hrBn : rootB 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0:ℂ),rootB t^2=B t) :
    ∃sigma : ℝ,0<sigma ∧ ∀s : ℝ,0<s → s<sigma →
      ∃A g D : ℝ,0<A ∧ 0<g ∧ 0<D ∧
      ∀ᶠ m : ℕ in atTop, ∀j : ℕ,8*(2*m+1)^2≤j →
      ‖2*(iteratedDeriv j
          (centeredKernelIntegral B rootB phi hphi m (Real.pi/(2*m+1:ℕ)) s) 0/(j.factorial:ℂ))-
          physicalModel B rootB phi (2*m+1) j‖≤
        A*((2*m+1:ℕ)/Real.sqrt j+(2*m+1:ℕ)^2/j+Real.exp (-(j:ℝ)*Real.log 2/8))*
          ‖physicalModel B rootB phi (2*m+1) j‖+
        gaussianEnvelope g D (2*m+1) j := by
  obtain ⟨delta,sigma,hd,hsigma,hex⟩ :=
    exists_actual_central_gaussian_model_error B rootB phi hphi hB hBn hrB hrBn hsq
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
  filter_upwards [hbound s hs hss hbs] with m hm
  intro j hj
  simpa only [physicalModel,centralHessian_at_winding,gaussianEnvelope] using hm j hj

end
end IsingBulk.Anisotropic.NegativeNormalForm
