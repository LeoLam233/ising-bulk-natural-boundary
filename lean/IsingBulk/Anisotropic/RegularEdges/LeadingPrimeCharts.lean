import IsingBulk.Anisotropic.RegularEdges.LeadingParityHigh
import IsingBulk.Anisotropic.RegularEdges.LeadingParityLow
import IsingBulk.Anisotropic.RegularEdges.PhasePrime

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail FormFactors Set Filter
open scoped Topology

theorem highPhysicalChartSeries_eq (lam : ℝ) (zeta A : ℂ→ℂ) (u : ℂ) :
    highPhysicalChartSeries lam zeta A u = A u * ∑'i,
      (spectralProduct lam (zeta u))^i*unscaledFullCoefficient (2*i+1) lam (zeta u) := by
  unfold highPhysicalChartSeries selectedPhysicalChartSeries
  simp only [id_eq,mul_assoc,tsum_mul_left]

theorem lowPhysicalChartSeries_eq (lam : ℝ) (zeta : ℂ→ℂ) (u : ℂ) :
    lowPhysicalChartSeries lam zeta u = ∑'i,
      (spectralProduct lam (zeta u))^(i+1)*unscaledFullCoefficient (2*i+2) lam (zeta u) := by
  unfold lowPhysicalChartSeries selectedPhysicalChartSeries
  simp only [one_mul,Nat.add_assoc]

theorem domain_extension_mul_analyticAt {D : Set ℂ} {f A : ℂ→ℂ} {z : ℂ}
    (hA : AnalyticAt ℂ A z) (hf : HasDomainExtension D f z) :
    HasDomainExtension D (fun u => A u*f u) z := by
  obtain ⟨V,hV,hzV,g,hg,heq⟩ := hf
  refine ⟨V∩{u | AnalyticAt ℂ A u},hV.inter (isOpen_analyticAt ℂ A),⟨hzV,hA⟩,
    (fun u => A u*g u),?_,?_⟩
  · intro u hu
    exact hu.2.mul (hg u hu.1)
  · intro u hu
    exact congrArg (fun v => A u*v) (heq ⟨hu.1.1,hu.2⟩)

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

/-- No analytic continuation of the actual unweighted HT parity sum across a prime regular chart. -/
theorem high_prime_chart_no_extension (hprime : b∈primePhaseCosines) :
    ¬HasDomainExtension U (fun u => ∑'i,
      (spectralProduct lam (zeta u))^i*unscaledFullCoefficient (2*i+1) lam (zeta u)) 0 := by
  obtain ⟨q,j,hq,hcritical,hres,hearly⟩ := primeCosine_first_odd hprime
  have hno := (highPhysicalChart_first_singularity hU ha hAa hz hs hB hS he hup hBi hlam hphysical
    hb hBa hBi0 hSa hS0 hzeta0 hA0 hAne hp0 hAsq hin hq hcritical hres hearly).2.2
  intro hf
  apply hno
  exact domain_extension_of_eqOn (fun u _ => highPhysicalChartSeries_eq lam zeta A u)
    (domain_extension_mul_analyticAt hA0 hf)

/-- No analytic continuation of the actual LT parity sum across a prime regular chart. -/
theorem low_prime_chart_no_extension (hprime : b∈primePhaseCosines) :
    ¬HasDomainExtension U (fun u => ∑'i,
      (spectralProduct lam (zeta u))^(i+1)*unscaledFullCoefficient (2*i+2) lam (zeta u)) 0 := by
  obtain ⟨q,j,hcritical,hres,hearly⟩ := primeCosine_first_even hprime
  have hno := (lowPhysicalChart_first_singularity hU ha hAa hz hs hB hS he hup hBi hlam hphysical
    hb hBa hBi0 hSa hS0 hzeta0 hA0 hAne hp0 hAsq hin hcritical hres hearly).2.2
  exact no_domain_extension_of_eqOn (fun u _ => lowPhysicalChartSeries_eq lam zeta u) hno

end Chart
end
end IsingBulk.Anisotropic.RegularEdges
