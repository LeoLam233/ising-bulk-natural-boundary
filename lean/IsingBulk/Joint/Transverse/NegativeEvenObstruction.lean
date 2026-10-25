import IsingBulk.Joint.Transverse.NegativeLocalSide
import IsingBulk.Joint.Transverse.PositiveObstruction

/-! # Actual full even-sum obstruction at the negative endpoint
The genuine pi-shift sign is absorbed into the analytic one-body scale, and
all higher differentiated orders are controlled by the proved full tail.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter Metric
open IsingBulk.Anisotropic IsingBulk.Anisotropic.RegularEdges
open RegularEdges
open scoped Topology

theorem normalized_negative_even_low_no_extension {curve : ℂ → Coupling} {b : ℝ}
    (hc : AnalyticAt ℂ curve 0) (hK : curve 0∈frontier lowDomain)
    (hS : S (curve 0)≠0) (hp : p (curve 0)^2≠1)
    (hB : 0<(negativeCurveB curve 0).im) (hb : |b|<1) (hprime : b∈primePhaseCosines)
    (hn : ∀ᶠ u in 𝓝 (0:ℂ), negativeParameter b (curve u)=u) :
    ¬HasFullExtension (curve ⁻¹' lowDomain) (FormFactors.lowNormalizedBulk ∘ curve) 0 := by
  have he0 : negativeParameter b (curve 0)=0 := Filter.EventuallyEq.eq_of_nhds hn
  obtain ⟨U,hU,h0U,hUf,hside⟩ := negativeFace_low_side hK hS hp hB hb he0
  have hBa := negativeCurveB_analyticAt hc hS
  have hSa : AnalyticAt ℂ (fun v => Complex.I*curveS curve v) 0 :=
    analyticAt_const.mul (curveS_analyticAt hc)
  have hSi : Complex.I*curveS curve 0≠0 := mul_ne_zero Complex.I_ne_zero hS
  have hP0 : p (curve 0)≠0 := by
    apply mul_ne_zero hS
    intro ht
    have hh : negativeCurveB curve 0=0 := by simp [negativeCurveB,transferB,ht]
    rw [hh,Complex.zero_im] at hB
    exact lt_irrefl _ hB
  have hPa := (FormFactors.p_analyticAt_normalized (curve 0)).comp hc
  have hHa := (lowPrefactor_boundary_analyticAt hK.1 hp).comp hc
  obtain ⟨δ,hδ,hno⟩ := normalized_prime_upperBall_no_extension hb hprime hBa hB hSa hSi
    hPa hP0 hHa (FormFactors.lowPrefactor_ne_zero (curve 0))
    hHa (FormFactors.lowPrefactor_ne_zero (curve 0))
  have hlocal : ∀ᶠ u in 𝓝 (0:ℂ), curve u∈U ∧ negativeParameter b (curve u)=u :=
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
  have hfull (n : ℕ) (hn : Even (n+1)) : FormFactors.unscaledFullCoefficient (n+1) (curve u)=
      angularCoefficient n b (negativeCurveB curve) (fun v => Complex.I*curveS curve v) u :=
    (fullCoefficient_eq_physicalAngular_low n hdom).trans
      (physicalAngular_eq_negative_even_model hn (lowDomain_subset_spectralComplement hdom)
        hface.1 hloc.2 hu.2.2 hface.2.1)
  have heq : FormFactors.lowNormalizedBulk (curve u)=
      FormFactors.lowPrefactor (curve u)*weightedEvenSeries b (negativeCurveB curve) (fun v => Complex.I*curveS curve v)
        (fun v => p (curve v)) u := by
    unfold FormFactors.lowNormalizedBulk weightedEvenSeries
    congr 1
    apply tsum_congr
    intro i
    rw [show 2*i+2=(2*i+1)+1 by omega,hfull (2*i+1) ⟨i+1,by omega⟩]
  exact (hgf ⟨hu.1,hdom⟩).trans heq


/-- The full low-temperature sum is obstructed on every nonramified analytic
curve at a selected negative phase, with its actual varying complex B. -/
theorem negative_even_low_curve_no_extension {curve : ℂ → Coupling} {z : ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ curve z) (hK : curve z∈frontier lowDomain)
    (hS : S (curve z)≠0) (hp : p (curve z)^2≠1)
    (hB : 0<(negativeCurveB curve z).im) (hb : |b|<1) (hprime : b∈primePhaseCosines)
    (he : negativeParameter b (curve z)=0)
    (hd : deriv (fun t => negativeParameter b (curve t)) z≠0) :
    ¬HasFullExtension (curve ⁻¹' lowDomain) (FormFactors.lowNormalizedBulk ∘ curve) z := by
  obtain ⟨ψ,hψ,hψ0,hn,_⟩ := exists_nonramified_inverse
    (negativeParameter_analyticAt b hc hS) he hd
  have hna : AnalyticAt ℂ (curve ∘ ψ) 0 := hc.comp_of_eq hψ hψ0
  intro hext
  apply normalized_negative_even_low_no_extension hna
    (by simpa [Function.comp_apply,hψ0] using hK)
    (by simpa [Function.comp_apply,hψ0] using hS)
    (by simpa [Function.comp_apply,hψ0] using hp)
    (by simpa [negativeCurveB,Function.comp_apply,hψ0] using hB) hb hprime hn
  have hext' := fullExtension_pullback hψ hψ0 hext
  exact hext'

end
end IsingBulk.Joint.Transverse
