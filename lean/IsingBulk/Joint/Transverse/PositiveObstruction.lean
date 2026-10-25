import IsingBulk.Joint.Transverse.LocalSide
import IsingBulk.Joint.RegularEdges.PhysicalIdentity
import IsingBulk.Joint.RegularEdges.NormalFormIdentity
import IsingBulk.Joint.RegularEdges.BoundaryPrefactors
import IsingBulk.Joint.RegularEdges.WeightedFullSum
import IsingBulk.Joint.Final.LocalExtension

/-! # Full physical obstructions on every nonramified positive-edge curve
Both the series and the intersected physical domains are the literal joint
objects. The varying complex anisotropy is retained through normalization.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter Metric
open IsingBulk.Anisotropic IsingBulk.Anisotropic.RegularEdges
open RegularEdges
open scoped Topology

theorem curve_p_ne_zero {curve : ℂ → Coupling} {t : ℂ}
    (hS : S (curve t)≠0) (hB : 0<(curveB curve t).im) : p (curve t)≠0 := by
  apply mul_ne_zero hS
  intro ht
  have hh : curveB curve t=0 := by simp [curveB,transferB,ht]
  rw [hh,Complex.zero_im] at hB
  exact lt_irrefl _ hB

theorem normalized_positive_high_no_extension {curve : ℂ → Coupling} {b : ℝ}
    (hc : AnalyticAt ℂ curve 0) (hK : curve 0∈frontier highDomain)
    (hS : S (curve 0)≠0) (hp : p (curve 0)^2≠1)
    (hB : 0<(curveB curve 0).im) (hb : |b|<1) (hprime : b∈primePhaseCosines)
    (hn : ∀ᶠ u in 𝓝 (0:ℂ), positiveParameter b (curve u)=u) :
    ¬HasFullExtension (curve ⁻¹' highDomain) (FormFactors.highNormalizedBulk ∘ curve) 0 := by
  have he0 : positiveParameter b (curve 0)=0 := Filter.EventuallyEq.eq_of_nhds hn
  obtain ⟨U,hU,h0U,hUf,hside⟩ := positiveFace_high_side hK hS hp hB hb he0
  have hBa := curveB_analyticAt hc hS
  have hSa := curveS_analyticAt hc
  have hPa := (FormFactors.p_analyticAt_normalized (curve 0)).comp hc
  have hHa := (highPrefactor_boundary_analyticAt hK.1 hp).comp hc
  obtain ⟨δ,hδ,hno⟩ := normalized_prime_upperBall_no_extension hb hprime hBa hB hSa hS
    hPa (curve_p_ne_zero hS hB) hHa (FormFactors.highPrefactor_ne_zero (curve 0))
    hHa (FormFactors.highPrefactor_ne_zero (curve 0))
  have hlocal : ∀ᶠ u in 𝓝 (0:ℂ), curve u∈U ∧ positiveParameter b (curve u)=u :=
    Filter.Eventually.and (hc.continuousAt.preimage_mem_nhds (hU.mem_nhds h0U)) hn
  obtain ⟨ε,hε,hεb⟩ := Metric.mem_nhds_iff.mp hlocal
  let r := min δ ε
  have hr : 0<r := lt_min hδ hε
  rintro ⟨V,hV,h0V,g,hg,hgf⟩
  apply (hno r hr (min_le_left _ _)).1
  refine ⟨V,hV,h0V,g,hg,?_⟩
  intro u hu
  have hloc := hεb (ball_subset_ball (min_le_right δ ε) hu.2.1)
  have hdom : curve u∈highDomain := (hside _ hloc.1).mpr (by rw [hloc.2]; exact hu.2.2)
  have hface := hUf hloc.1
  have hfull (n : ℕ) : FormFactors.unscaledFullCoefficient (n+1) (curve u)=
      angularCoefficient n b (curveB curve) (curveS curve) u :=
    (fullCoefficient_eq_physicalAngular_high n hdom hface.1).trans
      (physicalAngular_eq_positiveCoefficient n (highDomain_subset_spectralComplement hdom)
        hface.1 hloc.2 hu.2.2 hface.2.1)
  have heq : FormFactors.highNormalizedBulk (curve u)=
      FormFactors.highPrefactor (curve u)*weightedOddSeries b (curveB curve) (curveS curve)
        (fun v => p (curve v)) u := by
    unfold FormFactors.highNormalizedBulk weightedOddSeries
    congr 1
    apply tsum_congr
    intro i
    rw [hfull]
  exact (hgf ⟨hu.1,hdom⟩).trans heq

theorem normalized_positive_low_no_extension {curve : ℂ → Coupling} {b : ℝ}
    (hc : AnalyticAt ℂ curve 0) (hK : curve 0∈frontier lowDomain)
    (hS : S (curve 0)≠0) (hp : p (curve 0)^2≠1)
    (hB : 0<(curveB curve 0).im) (hb : |b|<1) (hprime : b∈primePhaseCosines)
    (hn : ∀ᶠ u in 𝓝 (0:ℂ), positiveParameter b (curve u)=u) :
    ¬HasFullExtension (curve ⁻¹' lowDomain) (FormFactors.lowNormalizedBulk ∘ curve) 0 := by
  have he0 : positiveParameter b (curve 0)=0 := Filter.EventuallyEq.eq_of_nhds hn
  obtain ⟨U,hU,h0U,hUf,hside⟩ := positiveFace_low_side hK hS hp hB hb he0
  have hBa := curveB_analyticAt hc hS
  have hSa := curveS_analyticAt hc
  have hPa := (FormFactors.p_analyticAt_normalized (curve 0)).comp hc
  have hHa := (lowPrefactor_boundary_analyticAt hK.1 hp).comp hc
  obtain ⟨δ,hδ,hno⟩ := normalized_prime_upperBall_no_extension hb hprime hBa hB hSa hS
    hPa (curve_p_ne_zero hS hB) hHa (FormFactors.lowPrefactor_ne_zero (curve 0))
    hHa (FormFactors.lowPrefactor_ne_zero (curve 0))
  have hlocal : ∀ᶠ u in 𝓝 (0:ℂ), curve u∈U ∧ positiveParameter b (curve u)=u :=
    Filter.Eventually.and (hc.continuousAt.preimage_mem_nhds (hU.mem_nhds h0U)) hn
  obtain ⟨ε,hε,hεb⟩ := Metric.mem_nhds_iff.mp hlocal
  let r := min δ ε
  have hr : 0<r := lt_min hδ hε
  rintro ⟨V,hV,h0V,g,hg,hgf⟩
  apply (hno r hr (min_le_left _ _)).2
  refine ⟨V,hV,h0V,g,hg,?_⟩
  intro u hu
  have hloc := hεb (ball_subset_ball (min_le_right δ ε) hu.2.1)
  have hdom : curve u∈lowDomain := (hside _ hloc.1).mpr (by rw [hloc.2]; exact hu.2.2)
  have hface := hUf hloc.1
  have hfull (n : ℕ) : FormFactors.unscaledFullCoefficient (n+1) (curve u)=
      angularCoefficient n b (curveB curve) (curveS curve) u :=
    (fullCoefficient_eq_physicalAngular_low n hdom).trans
      (physicalAngular_eq_positiveCoefficient n (lowDomain_subset_spectralComplement hdom)
        hface.1 hloc.2 hu.2.2 hface.2.1)
  have heq : FormFactors.lowNormalizedBulk (curve u)=
      FormFactors.lowPrefactor (curve u)*weightedEvenSeries b (curveB curve) (curveS curve)
        (fun v => p (curve v)) u := by
    unfold FormFactors.lowNormalizedBulk weightedEvenSeries
    congr 1
    apply tsum_congr
    intro i
    rw [show 2*i+2=(2*i+1)+1 by omega,hfull]
  exact (hgf ⟨hu.1,hdom⟩).trans heq

/-- Every holomorphic transverse curve with nonzero edge-coordinate derivative,
not merely a preferred constant-B line, has the physical high obstruction. -/
theorem positive_high_curve_no_extension {curve : ℂ → Coupling} {z : ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ curve z) (hK : curve z∈frontier highDomain)
    (hS : S (curve z)≠0) (hp : p (curve z)^2≠1)
    (hB : 0<(curveB curve z).im) (hb : |b|<1) (hprime : b∈primePhaseCosines)
    (he : positiveParameter b (curve z)=0)
    (hd : deriv (fun t => positiveParameter b (curve t)) z≠0) :
    ¬HasFullExtension (curve ⁻¹' highDomain) (FormFactors.highNormalizedBulk ∘ curve) z := by
  obtain ⟨ψ,nc,hψ,hψ0,hnc,hna,hn0,_,hn,_⟩ := normalize_positive_curve hc hS he hd
  intro hext
  have hext' := fullExtension_pullback hψ hψ0 hext
  apply normalized_positive_high_no_extension hna (hn0 ▸ hK) (hn0 ▸ hS) (hn0 ▸ hp)
    (by simpa only [curveB,hn0] using hB) hb hprime hn
  subst nc
  exact hext'

theorem positive_low_curve_no_extension {curve : ℂ → Coupling} {z : ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ curve z) (hK : curve z∈frontier lowDomain)
    (hS : S (curve z)≠0) (hp : p (curve z)^2≠1)
    (hB : 0<(curveB curve z).im) (hb : |b|<1) (hprime : b∈primePhaseCosines)
    (he : positiveParameter b (curve z)=0)
    (hd : deriv (fun t => positiveParameter b (curve t)) z≠0) :
    ¬HasFullExtension (curve ⁻¹' lowDomain) (FormFactors.lowNormalizedBulk ∘ curve) z := by
  obtain ⟨ψ,nc,hψ,hψ0,hnc,hna,hn0,_,hn,_⟩ := normalize_positive_curve hc hS he hd
  intro hext
  have hext' := fullExtension_pullback hψ hψ0 hext
  apply normalized_positive_low_no_extension hna (hn0 ▸ hK) (hn0 ▸ hS) (hn0 ▸ hp)
    (by simpa only [curveB,hn0] using hB) hb hprime hn
  subst nc
  exact hext'

end
end IsingBulk.Joint.Transverse
