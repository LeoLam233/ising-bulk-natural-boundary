import IsingBulk.Anisotropic.NegativeDominance.ActualPaperRadius
import IsingBulk.Anisotropic.NegativeDominance.NegativePaperCompleteData
import IsingBulk.Anisotropic.NegativeDominance.PrimeNegativePhase
import IsingBulk.Anisotropic.NegativeDominance.PhysicalOuterGaussian
import IsingBulk.Anisotropic.NegativeDominance.NonresonantGaussian

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set Filter Metric MeasureTheory FormFactors RegularEdges NegativeCycles
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

/-- Genuine negative regular prime HT endpoint. The actual infinite odd
particle series, all winding sectors, the physical prefactor and the original
physical domain are handled internally. No coefficient, dominance, radius,
or analytic-extension assumption remains. -/
theorem high_negative_prime_no_extension {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaH lam)) (hd : spectralDet lam z<0)
    (hv : spectralV lam z= -1) (hu : |spectralU lam z|<1)
    (hder : deriv (edgeMapV lam (-1)) z≠0) (hprime : spectralU lam z∈primePhaseCosines) :
    ¬HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  obtain ⟨p,phi,hp,hpo,hphi0,hphipi,hphi,hcos,hphase,hres⟩ := exists_prime_negative_phase hprime
  obtain ⟨zeta,A,hz0,hza,hAa,hA0,hpaper,_hinside,hretained,hjets,hlow,hnonres⟩ :=
    exists_negative_paper_complete_data hlam hz hd hv hu hder p hp.two_le hphase
  obtain ⟨Z,f,r,hr,hZ0,hf0,hZ,hf,hzeta,hmap,hin,hAdef,hAr,hdata⟩ := hretained
  have h0 : (0:ℂ)∈ball 0 r := mem_ball_self hr
  have hS0 : spectralS (zeta 0)≠0 := by rw [hz0]; exact spectralS_ne_zero_of_det_ne_zero hd.ne
  have hedgeZ : spectralA lam (Z 0)+spectralT lam (Z 0)=
      (spectralU lam z:ℂ)*spectralS (Z 0) := by
    rw [hZ0,spectral_reconstruction hd.ne,hv]
    simp only [Complex.ofReal_neg,Complex.ofReal_one]
    ring
  have hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=
      (Real.cos phi:ℂ)*spectralS (zeta 0) := by
    simpa only [hZ0,hz0,hcos] using hedgeZ
  have hBi : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im := by
    rw [hz0]
    exact negative_ratio_im_pos hd
  obtain ⟨hB,hB0,hrB,hrB0,hsq⟩ := paper_model_data hd hz0 hza hAa hA0 (hpaper.mono fun _ ht=>ht.1)
  have hchart : ∀ᶠt in 𝓝 (0:ℂ),spectralS (zeta t)≠0 ∧
      paperModelB lam zeta t=spectralT lam (zeta t)/spectralS (zeta t) ∧
      edgeMapV lam (-1) (zeta t)=(Real.cos phi:ℂ)+paperModelB lam zeta t*t ∧
      A t^2=spectralProduct lam (zeta t) ∧ A t/spectralS (zeta t)=paperModelRoot zeta A t := by
    filter_upwards [hpaper,(negativeChartS_analyticAt hza).continuousAt.eventually_ne hS0] with t ht hs
    exact ⟨hs,rfl,by simpa only [hcos,paperModelB] using ht.2,ht.1,rfl⟩
  have houter : ∀s : ℝ,0<s → ∃g D : ℝ,0<g ∧ 0<D ∧ ∀m j : ℕ,
      ‖∫v in physicalOuterRegion (2*m) s,physicalDensityTaylor (2*m) lam zeta A j v‖≤
        gaussianEnvelope g D (2*m+1) j := by
    intro s hs
    rw [hzeta,hAdef]
    exact physical_outer_jet_gaussian hr (hZ 0 h0) (hAr 0 h0)
      (hdata 0 h0).2.2.1 (hdata 0 h0).2.1 hedgeZ hu (hdata 0 h0).1 hf hf0
      (fun u hu=>⟨(hdata u hu.1).2.2.2.1,(hdata u hu.1).1⟩) hin s hs
  obtain ⟨a,D,ha,hD,hlow⟩ := hlow
  obtain ⟨an,rn,Cn,Mn,Kn,han,hrn,hrn1,hCn,hMn,hKn,hnonres⟩ := hnonres
  obtain ⟨aR,CR,haR,_hCR,hng⟩ := nonresonant_cauchy_gaussian han hrn hrn1 hCn hMn hKn p
    (fun n t=>A t^(n+1)*continuedAngularCoefficient n lam (zeta t)) hnonres
  have hzero := actual_negative_paper_radius_zero (paperModelB lam zeta) (paperModelRoot zeta A)
    phi hphi hphi0 hphipi hB hB0 hrB hrB0 hsq lam zeta A hza hAa hS0 hedge
    (by simpa only [hcos] using hu) hBi hchart houter p hp.pos hpo
    (fun m hm=>hres (2*m+1) hm) a D aR CR ha hD.le haR
    (fun j m=>hlow j (2*m) ⟨m,by omega⟩)
    (fun j m hm=>by
      simpa only [negativePaperParticleCoefficient,gaussianEnvelope,Nat.cast_add,Nat.cast_one] using
        hng j (2*m) ⟨m,by omega⟩ hm)
  exact negative_paper_chart_no_extension hlam hd hu hr hZ0 hf0 hZ hf hzeta hAa
    hmap hin (fun j=>(hjets j).2) hzero

end
end IsingBulk.Anisotropic.NegativeDominance
