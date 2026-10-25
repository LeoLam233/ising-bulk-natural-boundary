import IsingBulk.Joint.Negative.PhysicalCurveJets
import IsingBulk.Joint.Negative.CurveRadius
import IsingBulk.Joint.RegularEdges.BoundaryPrefactors
import IsingBulk.Anisotropic.NegativeDominance.BoundaryJetObstruction
import IsingBulk.Anisotropic.RegularEdges.LeadingPrimeCharts
import IsingBulk.Anisotropic.Final.AnalyticFactor

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
open scoped Topology

/-- No genuine physical full-HT extension along any normalized negative
transversal at a prime phase. All contour-series boundary jets and zero radius
are proved inside, not included as premises. -/
theorem normalized_negative_curve_no_extension {curve : ℂ→Coupling} {amp : ℂ→ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ curve 0) (ha : AnalyticAt ℂ amp 0)
    (hs : S (curve 0)≠0) (hB : (transferB (curve 0)).im<0)
    (hK : curve 0∈frontier highDomain) (hp : p (curve 0)^2≠1)
    (hprime : b∈primePhaseCosines)
    (he : ∀ᶠt in 𝓝 (0:ℂ),transferC (curve t)+transferB (curve t)=
      (b:ℂ)+transferB (curve t)*t)
    (hsq : ∀ᶠt in 𝓝 (0:ℂ),amp t^2=p (curve t)) :
    ¬HasDomainExtension (curve ⁻¹' highDomain) (FormFactors.highNormalizedBulk∘curve) 0 := by
  have hT : T (curve 0)≠0 := by
    intro h
    exact transferB_ne_zero_of_im_neg hB (by simp [transferB,h])
  have hP : p (curve 0)≠0 := mul_ne_zero hs hT
  have ha0 : amp 0≠0 := by
    intro h
    have hh := hsq.self_of_nhds
    rw [h,zero_pow (by decide : (2:ℕ)≠0)] at hh
    exact hP hh.symm
  obtain ⟨D⟩ := exists_upperNormalization hc ha hs ha0 hB he hsq
  obtain ⟨p0,phi,_,_,_,_,hphi,hcos,_,_⟩ := exists_prime_negative_phase hprime
  have hb : |b|<1 := by
    rw [hcos]
    exact (sq_lt_one_iff_abs_lt_one _).mp (by
      nlinarith [Real.sin_sq_add_cos_sq phi,sq_pos_of_ne_zero hphi])
  obtain ⟨V,hV,hmap,hin,hjets⟩ := D.physical_boundary_jets hb hK hp
  have hpath : Tendsto (fun ε : ℝ=>-(ε:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous (fun ε : ℝ=>-(ε:ℂ)) := Complex.continuous_ofReal.neg
    simpa only [Complex.ofReal_zero,neg_zero] using
      (h.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
  have h0 : (0:ℂ)∈ball 0 D.radius := mem_ball_self D.radius_pos
  let Z : ℂ→Coupling := fun t=>D.Z (D.f t)
  have hZ0 : Z 0=curve 0 := D.curve_eq.eq_of_nhds.symm
  have hZa : AnalyticAt ℂ Z 0 := (D.Z_analytic 0 h0).comp_of_eq D.f_analytic D.f_zero
  let pref : ℂ→ℂ := fun t=>FormFactors.highPrefactor (Z t)
  have hpa : AnalyticAt ℂ pref 0 :=
    (RegularEdges.highPrefactor_boundary_analyticAt (by rw [hZ0]; exact hK.1) (by rwa [hZ0])).comp hZa
  have hpn : pref 0≠0 := FormFactors.highPrefactor_ne_zero _
  let raw : ℂ→ℂ := fun t=>∑'n : ℕ,p (Z t)^n*FormFactors.unscaledFullCoefficient (2*n+1) (Z t)
  have hwa : AnalyticAt ℂ (fun t=>D.weight (D.f t)) 0 :=
    (D.weight_analytic 0 h0).comp_of_eq D.f_analytic D.f_zero
  intro hext
  obtain ⟨W,hW,h0W,g,hg,hge⟩ := hext
  obtain ⟨W0,hW0sub,hW0,h0W0⟩ := _root_.mem_nhds_iff.mp D.curve_eq
  have hext' : HasDomainExtension V (pref*raw) 0 := by
    refine ⟨W∩W0,hW.inter hW0,⟨h0W,h0W0⟩,g,hg.mono inter_subset_left,?_⟩
    intro t ht
    have heq : curve t=Z t := hW0sub ht.1.2
    have htH : curve t∈highDomain := by rw [heq]; exact hmap ht.2
    have hh := hge ⟨ht.1.1,htH⟩
    simpa only [Function.comp_apply,heq,FormFactors.highNormalizedBulk,Pi.mul_apply,pref,raw] using hh
  have hraw := domain_extension_of_analytic_factor hpa hpn hext'
  have hweighted := domain_extension_mul_analyticAt hwa hraw
  exact no_domain_extension_of_boundary_jets_zero_radius (negativePaperCoefficient curve amp)
    hV hpath hin (fun j=>(hjets j).2)
    (normalized_negative_curve_radius_zero hc ha hs hB hprime he hsq) hweighted

end
end IsingBulk.Joint.Negative
