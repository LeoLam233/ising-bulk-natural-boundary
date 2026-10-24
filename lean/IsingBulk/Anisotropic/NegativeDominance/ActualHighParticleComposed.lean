import IsingBulk.Anisotropic.NegativeDominance.ActualHighParticle
import IsingBulk.Anisotropic.NegativeDominance.PhysicalOuterGaussian

noncomputable section
namespace IsingBulk.Anisotropic.NegativeDominance
open NegativeCycles RegularEdges Set Filter
open scoped Topology

/-- End-to-end high-particle estimate on the original upper chart and its actual
paper parameter. In particular, no outer-integral estimate remains a premise. -/
theorem actual_resonant_high_particle_composed_bound
    {lam phi r0 : ℝ} {Z A f B rootB : ℂ→ℂ}
    (hphi : Real.sin phi≠0) (hp : 0<phi) (hpi : phi<Real.pi)
    (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) (hrB : AnalyticAt ℂ rootB 0)
    (hr0 : 0<r0) (hZ : AnalyticAt ℂ Z 0) (hA : AnalyticAt ℂ A 0) (hA0 : A 0≠0)
    (hS0 : spectralS (Z 0)≠0)
    (hedge : spectralA lam (Z 0)+spectralT lam (Z 0)=(Real.cos phi:ℂ)*spectralS (Z 0))
    (hBi : 0<(negativeChartB lam Z 0).im)
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0)
    (hdata : ∀u∈upperBall r0,edgeMapV lam (-1) (Z u)=(Real.cos phi:ℂ)+u ∧
      0<(negativeChartB lam Z u).im)
    (hin : ∀ᶠ ε : ℝ in 𝓝[>] 0,f (-(ε:ℂ))∈upperBall r0)
    (hchart : ∀ᶠt in 𝓝 (0:ℂ), spectralS (Z (f t))≠0 ∧
      B t=spectralT lam (Z (f t))/spectralS (Z (f t)) ∧
      edgeMapV lam (-1) (Z (f t))=(Real.cos phi:ℂ)+B t*t ∧
      A (f t)^2=spectralProduct lam (Z (f t)) ∧ A (f t)/spectralS (Z (f t))=rootB t) :
    ∃g D Chigh : ℝ,0<g ∧ 0<D ∧ 0<Chigh ∧ ∀m j : ℕ,
      Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1 →
      ‖negativePaperParticleCoefficient lam (fun t=>Z (f t)) (fun t=>A (f t)) m j‖≤
        Real.exp (2*j*Real.log (2*m+1:ℕ)-((2*m+1:ℕ):ℝ)^2/2*Real.log (2*m+1:ℕ)+Chigh*((2*m+1:ℕ):ℝ)^2)+
          gaussianEnvelope g D (2*m+1) j := by
  have hZf : AnalyticAt ℂ (fun t=>Z (f t)) 0 :=
    (show AnalyticAt ℂ Z (f 0) by simpa only [hf0] using hZ).comp hf
  have hAf : AnalyticAt ℂ (fun t=>A (f t)) 0 :=
    (show AnalyticAt ℂ A (f 0) by simpa only [hf0] using hA).comp hf
  have hb : |Real.cos phi|<1 := (sq_lt_one_iff_abs_lt_one _).mp (by
    nlinarith [Real.sin_sq_add_cos_sq phi,sq_pos_of_ne_zero hphi])
  obtain ⟨g,D,Chigh,hg,hD,hC,hbound⟩ := actual_resonant_high_particle_bound B rootB phi hphi hp hpi hB hBn hrB lam
    (fun t=>Z (f t)) (fun t=>A (f t)) hZf hAf
    (by simpa only [hf0] using hS0) (by simpa only [hf0] using hedge)
    (by simpa only [negativeChartB,hf0] using hBi) hchart
    (fun s hs=>physical_outer_jet_gaussian hr0 hZ hA hA0 hS0 hedge hb hBi hf hf0 hdata hin s hs)

  exact ⟨g,D,Chigh,hg,hD,hC,fun m j hres=>hbound m (resonant_odd_free_index_pos hphi hres) j hres⟩

end IsingBulk.Anisotropic.NegativeDominance
