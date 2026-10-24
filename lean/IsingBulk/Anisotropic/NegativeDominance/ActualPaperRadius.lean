import IsingBulk.Anisotropic.NegativeDominance.ActualMiddleParticle
import IsingBulk.Anisotropic.NegativeDominance.ActualHighParticle
import IsingBulk.Anisotropic.NegativeDominance.ActualMiddleErrorScale
import IsingBulk.Anisotropic.NegativeDominance.CompleteCoefficientRadius

noncomputable section
namespace IsingBulk.Anisotropic.NegativeDominance
open IsingBulk.First NegativeNormalForm NegativeCycles RegularEdges
open Set MeasureTheory Filter
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

/-- Actual complete physical coefficient ranges, derived from the physical
residue decomposition and all-index estimates, not postulated dominance. -/
theorem actual_negative_paper_ranges (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hp : 0<phi) (hpi : phi<Real.pi)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) (hr0 : rootB 0≠0)
    (hsq : ∀ᶠt in 𝓝 (0:ℂ),rootB t^2=B t)
    (lam : ℝ) (zeta A : ℂ→ℂ) (hzeta : AnalyticAt ℂ zeta 0) (hA : AnalyticAt ℂ A 0)
    (hS : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(Real.cos phi:ℂ)*spectralS (zeta 0))
    (hb : |Real.cos phi|<1) (hBi : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im)
    (hchart : ∀ᶠt in 𝓝 (0:ℂ),spectralS (zeta t)≠0 ∧
      B t=spectralT lam (zeta t)/spectralS (zeta t) ∧
      edgeMapV lam (-1) (zeta t)=(Real.cos phi:ℂ)+B t*t ∧
      A t^2=spectralProduct lam (zeta t) ∧ A t/spectralS (zeta t)=rootB t)
    (houter : ∀s : ℝ,0<s → ∃g D : ℝ,0<g ∧ 0<D ∧ ∀m j : ℕ,
      ‖∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) lam zeta A j v‖≤
        gaussianEnvelope g D (2*m+1) j)
    (p : ℕ) (hp0 : 0<p) (hpOdd : Odd p)
    (hres : ∀m : ℕ,p∣2*m+1 → Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1)
    (a Dlow aR CR : ℝ) (ha : 0<a) (hDlow : 0≤Dlow) (haR : 0<aR)
    (hlow : ∀j m,‖negativePaperParticleCoefficient lam zeta A m j‖≤
      Dlow*((2*m+1:ℕ):ℝ)^2*(((2*m+1:ℕ):ℝ)^3/a)^j)
    (hnonres : ∀j m,¬p∣2*m+1 → ‖negativePaperParticleCoefficient lam zeta A m j‖≤
      gaussianEnvelope aR CR (2*m+1) j) :
    ∃E D C : ℝ,0<E ∧ 0<D ∧ ∀ᶠj : ℕ in atTop,
      HasCoefficientRanges (negativePaperCoefficient lam zeta A) B rootB phi p a D C (actualMiddleErrorScale E) j := by
  obtain ⟨E,gm,Dm,hE,hgm,hDm,hmiddle⟩ := exists_actual_middle_particle_bound B rootB phi hphi hp hpi hB hB0 hrB hr0 hsq
    lam zeta A hzeta hA hS hedge hb hBi hchart houter
  obtain ⟨gh,Dh,Ch,hgh,_hDh,_hCh,hhigh⟩ := actual_resonant_high_particle_bound B rootB phi hphi hp hpi hB hB0 hrB
    lam zeta A hzeta hA hS hedge hBi hchart houter
  let g := min gm gh
  let Dg := max Dm Dh
  have hgm' (N j : ℕ) := gaussianEnvelope_mono (min_le_left gm gh) (le_max_left Dm Dh) N j
  have hgh' (N j : ℕ) := gaussianEnvelope_mono (min_le_right gm gh) (le_max_right Dm Dh) N j
  have hm : ∀ᶠj : ℕ in atTop,∀m,p∣2*m+1 → Real.log j<((2*m+1:ℕ):ℝ) →
      ((2*m+1:ℕ):ℝ)^2≤j/Real.sqrt (Real.log j) →
      ‖negativePaperParticleCoefficient lam zeta A m j-physicalModel B rootB phi (2*m+1) j‖≤
        actualMiddleErrorScale E j*‖physicalModel B rootB phi (2*m+1) j‖+gaussianEnvelope g Dg (2*m+1) j := by
    filter_upwards [hmiddle] with j hj
    intro m hm hlo hcut
    exact (hj m hlo hcut (hres m hm)).trans (add_le_add (le_refl _) (hgm' (2*m+1) j))
  have hh : ∀ᶠj : ℕ in atTop,∀m,p∣2*m+1 → Real.log j<((2*m+1:ℕ):ℝ) →
      (j:ℝ)/Real.sqrt (Real.log j)<((2*m+1:ℕ):ℝ)^2 →
      ‖negativePaperParticleCoefficient lam zeta A m j‖≤
        Real.exp (2*j*Real.log (2*m+1)-((2*m+1:ℕ):ℝ)^2/2*Real.log (2*m+1)+Ch*((2*m+1:ℕ):ℝ)^2)+
        gaussianEnvelope g Dg (2*m+1) j := by
    have hl : Tendsto (fun j : ℕ=>Real.log (j:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hl.eventually_ge_atTop 3] with j hj
    intro m hm hlo _hcut
    have hm1 : 1≤m := by
      have hn : (3:ℝ)<(2*m+1:ℕ) := hj.trans_lt hlo
      have hn' : 3<2*m+1 := by exact_mod_cast hn
      omega
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      (hhigh m hm1 j (hres m hm)).trans (add_le_add (le_refl _) (hgh' (2*m+1) j))
  obtain ⟨D,C,hD,hranges⟩ := negative_paper_ranges_of_particle_estimates lam zeta A B rootB phi hp0 hpOdd ha hDlow
    (lt_min hgm hgh) haR Dg CR Ch (actualMiddleErrorScale E)
    (Filter.Eventually.of_forall (actualMiddleErrorScale_nonneg hE.le)) hlow hnonres hm hh
  exact ⟨E,D,C,hE,hD,hranges⟩

/-- The actual complete normalized negative-edge coefficient series has zero
radius, using only physical chart data and the independently proved Cauchy
bounds, with all resonant dominance estimates derived internally. -/
theorem actual_negative_paper_radius_zero (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hp : 0<phi) (hpi : phi<Real.pi)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) (hr0 : rootB 0≠0)
    (hsq : ∀ᶠt in 𝓝 (0:ℂ),rootB t^2=B t)
    (lam : ℝ) (zeta A : ℂ→ℂ) (hzeta : AnalyticAt ℂ zeta 0) (hA : AnalyticAt ℂ A 0)
    (hS : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(Real.cos phi:ℂ)*spectralS (zeta 0))
    (hb : |Real.cos phi|<1) (hBi : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im)
    (hchart : ∀ᶠt in 𝓝 (0:ℂ),spectralS (zeta t)≠0 ∧
      B t=spectralT lam (zeta t)/spectralS (zeta t) ∧
      edgeMapV lam (-1) (zeta t)=(Real.cos phi:ℂ)+B t*t ∧
      A t^2=spectralProduct lam (zeta t) ∧ A t/spectralS (zeta t)=rootB t)
    (houter : ∀s : ℝ,0<s → ∃g D : ℝ,0<g ∧ 0<D ∧ ∀m j : ℕ,
      ‖∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) lam zeta A j v‖≤
        gaussianEnvelope g D (2*m+1) j)
    (p : ℕ) (hp0 : 0<p) (hpOdd : Odd p)
    (hres : ∀m : ℕ,p∣2*m+1 → Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1)
    (a Dlow aR CR : ℝ) (ha : 0<a) (hDlow : 0≤Dlow) (haR : 0<aR)
    (hlow : ∀j m,‖negativePaperParticleCoefficient lam zeta A m j‖≤
      Dlow*((2*m+1:ℕ):ℝ)^2*(((2*m+1:ℕ):ℝ)^3/a)^j)
    (hnonres : ∀j m,¬p∣2*m+1 → ‖negativePaperParticleCoefficient lam zeta A m j‖≤
      gaussianEnvelope aR CR (2*m+1) j) :
    (FormalMultilinearSeries.ofScalars ℂ (negativePaperCoefficient lam zeta A)).radius=0 := by
  obtain ⟨E,D,C,_hE,hD,hranges⟩ := actual_negative_paper_ranges B rootB phi hphi hp hpi hB hB0 hrB hr0 hsq lam zeta A hzeta hA hS hedge hb hBi hchart houter p hp0 hpOdd hres a Dlow aR CR ha hDlow haR hlow hnonres
  exact complete_coefficient_radius_zero _ B rootB phi hB hB0 hrB.continuousAt hr0 hsq hphi p hp0 hpOdd
    ha hD (actualMiddleErrorScale_tendsto_zero E) hranges


/-- One and the same integer crossing order gives actual complete-coefficient
noncancellation and supergeometric growth along the resonant odd progression. -/
theorem actual_negative_paper_selected_growth (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hp : 0<phi) (hpi : phi<Real.pi)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hrB : AnalyticAt ℂ rootB 0) (hr0 : rootB 0≠0)
    (hsq : ∀ᶠt in 𝓝 (0:ℂ),rootB t^2=B t)
    (lam : ℝ) (zeta A : ℂ→ℂ) (hzeta : AnalyticAt ℂ zeta 0) (hA : AnalyticAt ℂ A 0)
    (hS : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(Real.cos phi:ℂ)*spectralS (zeta 0))
    (hb : |Real.cos phi|<1) (hBi : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im)
    (hchart : ∀ᶠt in 𝓝 (0:ℂ),spectralS (zeta t)≠0 ∧
      B t=spectralT lam (zeta t)/spectralS (zeta t) ∧
      edgeMapV lam (-1) (zeta t)=(Real.cos phi:ℂ)+B t*t ∧
      A t^2=spectralProduct lam (zeta t) ∧ A t/spectralS (zeta t)=rootB t)
    (houter : ∀s : ℝ,0<s → ∃g D : ℝ,0<g ∧ 0<D ∧ ∀m j : ℕ,
      ‖∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) lam zeta A j v‖≤
        gaussianEnvelope g D (2*m+1) j)
    (p : ℕ) (hp0 : 0<p) (hpOdd : Odd p)
    (hres : ∀m : ℕ,p∣2*m+1 → Complex.exp (((2*m+1:ℕ):ℂ)*((phi:ℂ)*Complex.I))=1)
    (a Dlow aR CR : ℝ) (ha : 0<a) (hDlow : 0≤Dlow) (haR : 0<aR)
    (hlow : ∀j m,‖negativePaperParticleCoefficient lam zeta A m j‖≤
      Dlow*((2*m+1:ℕ):ℝ)^2*(((2*m+1:ℕ):ℝ)^3/a)^j)
    (hnonres : ∀j m,¬p∣2*m+1 → ‖negativePaperParticleCoefficient lam zeta A m j‖≤
      gaussianEnvelope aR CR (2*m+1) j) :
    ∃K : ℝ,∃N : ℕ,∀ell : ℕ,N≤resonantParticle p ell → ∃j : ℕ,
      lowerCrossingOrder (resonantParticle p ell)-1<(j:ℝ) ∧
      (j:ℝ)≤upperCrossingOrder (resonantParticle p ell) ∧ resonantParticle p ell≤j ∧
      ‖physicalModel B rootB phi (resonantParticle p (ell+1)) j‖/2≤‖negativePaperCoefficient lam zeta A j‖ ∧
      Real.exp ((j:ℝ)*(2*Real.log (resonantParticle p ell)-K))/2≤‖negativePaperCoefficient lam zeta A j‖ := by
  obtain ⟨E,D,C,_hE,hD,hranges⟩ := actual_negative_paper_ranges B rootB phi hphi hp hpi hB hB0 hrB hr0 hsq lam zeta A hzeta hA hS hedge hb hBi hchart houter p hp0 hpOdd hres a Dlow aR CR ha hDlow haR hlow hnonres
  exact complete_coefficient_selected_growth _ B rootB phi hB hB0 hrB.continuousAt hr0 hsq hphi p hp0 hpOdd
    ha hD (actualMiddleErrorScale_tendsto_zero E) hranges

end IsingBulk.Anisotropic.NegativeDominance
