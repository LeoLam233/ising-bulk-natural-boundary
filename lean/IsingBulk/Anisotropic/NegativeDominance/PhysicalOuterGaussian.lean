import IsingBulk.Anisotropic.NegativeDominance.PhysicalOuterCauchy
import IsingBulk.Anisotropic.NegativeDominance.GaussianEnvelopeAlgebra
import IsingBulk.Anisotropic.NegativeCycles.OuterGaussianFamily

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set Filter Metric MeasureTheory RegularEdges NegativeCycles
open scoped Topology BigOperators

/-- A common Gaussian bound for every literal physical odd-particle outer
coefficient on the retained paper chart. The Cauchy and summability bounds
are derived internally, rather than supplied as an analytic premise. -/
theorem physical_outer_jet_gaussian {lam b : ℝ} {Z A f : ℂ→ℂ} {r0 : ℝ}
    (hr0 : 0<r0) (hZ : AnalyticAt ℂ Z 0) (hA : AnalyticAt ℂ A 0) (hA0 : A 0≠0)
    (hS0 : spectralS (Z 0)≠0)
    (hedge : spectralA lam (Z 0)+spectralT lam (Z 0)=(b:ℂ)*spectralS (Z 0))
    (hb : |b|<1) (hB0 : 0<(negativeChartB lam Z 0).im)
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0)
    (hdata : ∀u∈upperBall r0,edgeMapV lam (-1) (Z u)=(b:ℂ)+u ∧
      0<(negativeChartB lam Z u).im)
    (hin : ∀ᶠ ε : ℝ in 𝓝[>] 0,f (-(ε:ℂ))∈upperBall r0)
    (σ : ℝ) (hσ : 0<σ) :
    ∃g D : ℝ,0<g ∧ 0<D ∧ ∀m j : ℕ,
      ‖∫v in physicalOuterRegion (2*m) σ,
        physicalDensityTaylor (2*m) lam (fun t=>Z (f t)) (fun t=>A (f t)) j v‖≤
        gaussianEnvelope g D (2*m+1) j := by
  obtain ⟨a,r,C,M,K,ha,hr,hr1,hC,hM,_hK,hbound⟩ :=
    physical_outer_jet_cauchy hr0 hZ hA hA0 hS0 hedge hb hB0 hf hf0 hdata hin σ hσ
  obtain ⟨g,_Ds,L,_Q,hg,_hDs,hL,_hQ,hfamily⟩ :=
    selected_particle_coefficient_family_gaussian (K := K) (fun m : ℕ=>2*m+1)
      (by intro x y h; dsimp at h; omega) (fun m=>by omega) hr hr1 hC hM ha
  let F : ℕ→ℕ→ℂ := fun m j=>∫v in physicalOuterRegion (2*m) σ,
    physicalDensityTaylor (2*m) lam (fun t=>Z (f t)) (fun t=>A (f t)) j v
  have hF : ∀m j : ℕ,‖F m j‖≤
      K*particleEdgeMajorant r C M (2*m+1)*((2*m+1:ℕ)/a)^j := by
    intro m j
    exact hbound (2*m) j ⟨m,by omega⟩
  refine ⟨g,L,hg,hL,?_⟩
  intro m j
  exact (hfamily F hF).1 m j

end
end IsingBulk.Anisotropic.NegativeDominance
