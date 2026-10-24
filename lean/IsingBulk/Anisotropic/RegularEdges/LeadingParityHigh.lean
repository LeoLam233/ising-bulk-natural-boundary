import IsingBulk.Anisotropic.RegularEdges.LeadingSelected
import IsingBulk.Anisotropic.RegularEdges.LeadingArithmetic
import IsingBulk.Anisotropic.RegularEdges.LeadingTailTransfer

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail FormFactors Set Filter
open scoped Topology

def highPhysicalChartSeries (lam : ℝ) (zeta A : ℂ→ℂ) : ℂ→ℂ :=
  selectedPhysicalChartSeries (fun i => 2*i) id lam zeta A

section Chart
variable {lam b : ℝ} {U : Set ℂ} {zeta B S A : ℂ→ℂ}
variable (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U) (hAa : AnalyticOnNhd ℂ A U)
  (hz : ∀u∈U,zeta u∉spectralSet lam) (hs : ∀u∈U,spectralS (zeta u)≠0)
  (hB : ∀u∈U,B u=spectralT lam (zeta u)/spectralS (zeta u))
  (hS : ∀u∈U,S u=spectralS (zeta u))
  (he : ∀u∈U,edgeMapV lam 1 (zeta u)=(b:ℂ)+u)
  (hup : ∀u∈U,0<u.im) (hBi : ∀u∈U,0<(B u).im)
  (hlam : 0<lam) (hphysical : ∀u∈U,zeta u∈(omegaH lam\{0})∪omegaL lam)
  (hb : |b|<1) (hBa : AnalyticAt ℂ B 0) (hBi0 : 0<(B 0).im)
  (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0)
  (hzeta0 : AnalyticAt ℂ zeta 0) (hA0 : AnalyticAt ℂ A 0) (hAne : A 0≠0)
  (hp0 : spectralProduct lam (zeta 0)≠0)
  (hAsq : ∀u∈U,(A u)^2=spectralProduct lam (zeta u))
  (hin : ∀ᶠ t : ℝ in 𝓝[>] 0,Complex.I*(t:ℂ)^2∈U)
include hU ha hAa hz hs hB hS he hup hBi hlam hphysical hb hBa hBi0 hSa hS0 hzeta0 hA0 hAne hp0 hAsq hin

/-- The complete actual HT parity series has its first nonzero odd resonant amplitude.
The summable tail and every finite competing particle order are included. -/
theorem highPhysicalChart_first_singularity {q j : ℕ} (hq : 1≤q)
    (hcritical : 2*j+1=(2*q+1)^2) (hres : continuedRoot (b:ℂ)^(2*q+1)=1)
    (hearly : ∀i<q,continuedRoot (b:ℂ)^(2*i+1)≠1) :
    let C := (A 0*(spectralProduct lam (zeta 0))^q)*edgeCoefficientLeading (2*q) j b B S
    C≠0 ∧ Tendsto (fun t : ℝ => (t^2) • iteratedDeriv j
      (highPhysicalChartSeries lam zeta A) (Complex.I*(t:ℂ)^2)) (𝓝[>] 0) (𝓝 C) ∧
      ¬HasDomainExtension U (highPhysicalChartSeries lam zeta A) 0 := by
  dsimp only
  obtain ⟨hj,hdegree⟩ := odd_first_degree hq hcritical
  have hfull : edgeFullLeadingCoefficient (2*q) j b B S≠0 := by
    simpa [Nat.sub_add_cancel hj] using
      (odd_edge_full_leading_amplitude (by omega : 1≤2*q) hdegree hb hBa hBi0 hSa hS0 hres).1
  have hC : (A 0*(spectralProduct lam (zeta 0))^q)*edgeCoefficientLeading (2*q) j b B S≠0 :=
    mul_ne_zero (mul_ne_zero hAne (pow_ne_zero _ hp0))
      (mul_ne_zero (edgeCoefficientNormalization_ne_zero _) hfull)
  obtain ⟨GH,Glow,hGH,_,htail⟩ := physicalParity_tail_inward_majorants hb hBi0 hBa hSa hS0 hA0 hAne
    hU ha hAa hz hs hB hS he hup hBi hlam hphysical hAsq hin j
  have hlim : Tendsto (fun t : ℝ => (t^2) • iteratedDeriv j
      (highPhysicalChartSeries lam zeta A) (Complex.I*(t:ℂ)^2)) (𝓝[>] 0)
      (𝓝 ((A 0*(spectralProduct lam (zeta 0))^q)*edgeCoefficientLeading (2*q) j b B S)) := by
    apply selectedPhysicalChartSeries_first_limit hU ha hAa hz hs hB hS he hup hBi hlam hphysical
      hb hBa hBi0 hSa hS0 hzeta0 hA0 hin (fun i => 2*i) id
      (p := q) (L := j+2) (by omega : 0<2) (by nlinarith : q<j+2)
      (fun _ => by dsimp; omega) (fun _ hC => hadamardEnvelope_odd_summable hC)
      hres hearly (fun i hi _ => odd_higher_degree hcritical hi)
      (odd_first_balance hcritical) (odd_first_majorant_integrable hq hcritical) hGH
    filter_upwards [htail] with t ht i
    change ‖iteratedDeriv j (fun v => A v*(spectralProduct lam (zeta v))^(i+(j+2))*
      unscaledFullCoefficient (2*(i+(j+2))+1) lam (zeta v)) (Complex.I*(t:ℂ)^2)‖≤GH i
    rw [show i+(j+2)=j+2+i by omega]
    exact (ht i).1
  exact ⟨hC,hlim,no_domain_extension_of_scaled_jet_limit hU (by omega) hC hin hlim⟩

end Chart
end
end IsingBulk.Anisotropic.RegularEdges
