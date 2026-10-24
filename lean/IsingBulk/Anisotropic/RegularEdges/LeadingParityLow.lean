import IsingBulk.Anisotropic.RegularEdges.LeadingSelected
import IsingBulk.Anisotropic.RegularEdges.LeadingArithmetic
import IsingBulk.Anisotropic.RegularEdges.LeadingTailTransfer

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail FormFactors Set Filter
open scoped Topology

def lowPhysicalChartSeries (lam : ℝ) (zeta : ℂ→ℂ) : ℂ→ℂ :=
  selectedPhysicalChartSeries (fun i => 2*i+1) (fun i => i+1) lam zeta (fun _ => 1)

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

/-- The complete actual LT parity series has its first nonzero even resonant amplitude. -/
theorem lowPhysicalChart_first_singularity {q j : ℕ}
    (hcritical : 2*(j+1)=(2*q+2)^2) (hres : continuedRoot (b:ℂ)^(2*q+2)=1)
    (hearly : ∀i<q,continuedRoot (b:ℂ)^(2*i+2)≠1) :
    let C := (spectralProduct lam (zeta 0))^(q+1)*edgeCoefficientLeading (2*q+1) j b B S
    C≠0 ∧ Tendsto (fun t : ℝ => (t^1) • iteratedDeriv j
      (lowPhysicalChartSeries lam zeta) (Complex.I*(t:ℂ)^2)) (𝓝[>] 0) (𝓝 C) ∧
      ¬HasDomainExtension U (lowPhysicalChartSeries lam zeta) 0 := by
  dsimp only
  have hfull : edgeFullLeadingCoefficient (2*q+1) j b B S≠0 :=
    (even_edge_full_leading_amplitude (by omega : 1≤2*q+1) (even_first_degree hcritical)
      hb hBa hBi0 hSa hS0 (by simpa only [Nat.add_assoc] using hres)).1
  have hC : (spectralProduct lam (zeta 0))^(q+1)*edgeCoefficientLeading (2*q+1) j b B S≠0 :=
    mul_ne_zero (pow_ne_zero _ hp0) (mul_ne_zero (edgeCoefficientNormalization_ne_zero _) hfull)
  obtain ⟨GH,Glow,_,hGlow,htail⟩ := physicalParity_tail_inward_majorants hb hBi0 hBa hSa hS0 hA0 hAne
    hU ha hAa hz hs hB hS he hup hBi hlam hphysical hAsq hin j
  have hlim : Tendsto (fun t : ℝ => (t^1) • iteratedDeriv j
      (lowPhysicalChartSeries lam zeta) (Complex.I*(t:ℂ)^2)) (𝓝[>] 0)
      (𝓝 ((spectralProduct lam (zeta 0))^(q+1)*edgeCoefficientLeading (2*q+1) j b B S)) := by
    have hsel := selectedPhysicalChartSeries_first_limit hU ha
      (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (1:ℂ)) U)
      hz hs hB hS he hup hBi hlam hphysical hb hBa hBi0 hSa hS0 hzeta0 analyticAt_const hin
      (fun i => 2*i+1) (fun i => i+1) (p := q) (L := j+1) (j := j) (a := 1)
      (by omega) (by nlinarith : q<j+1) (fun _ => by omega)
      (fun C hC => by
        have hh := (hadamardEnvelope_even_summable hC).comp_injective Nat.succ_injective
        change Summable (fun i => hadamardEnvelope C (2*(i+1))) at hh
        simpa only [mul_add,mul_one,Nat.add_assoc] using hh)
      (by simpa only [Nat.add_assoc] using hres)
      (fun i hi => by simpa only [Nat.add_assoc] using hearly i hi)
      (fun i hi _ => even_higher_degree hcritical hi)
      (even_first_balance hcritical) (even_first_majorant_integrable hcritical) hGlow
      (by
        filter_upwards [htail] with t ht i
        rw [show i+(j+1)+1=j+2+i by omega,show 2*(i+(j+1))+1+1=2*(j+2+i) by omega]
        simpa only [one_mul] using (ht i).2)
    simpa only [one_mul,lowPhysicalChartSeries] using hsel
  exact ⟨hC,hlim,no_domain_extension_of_scaled_jet_limit hU (by omega) hC hin hlim⟩

end Chart
end
end IsingBulk.Anisotropic.RegularEdges
