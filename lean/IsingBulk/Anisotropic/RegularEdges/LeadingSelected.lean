import IsingBulk.Anisotropic.RegularEdges.LeadingPhysical
import IsingBulk.Anisotropic.RegularEdges.LeadingSeries
import IsingBulk.Anisotropic.RegularEdges.LeadingNonextension

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail FormFactors Set Filter MeasureTheory
open scoped Topology

def selectedPhysicalChartSeries (n k : ℕ→ℕ) (lam : ℝ) (zeta A : ℂ→ℂ) (u : ℂ) : ℂ :=
  ∑' i,A u*(spectralProduct lam (zeta u))^(k i)*unscaledFullCoefficient (n i+1) lam (zeta u)

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
  (hzeta0 : AnalyticAt ℂ zeta 0) (hA0 : AnalyticAt ℂ A 0)
  (hin : ∀ᶠ t : ℝ in 𝓝[>] 0,Complex.I*(t:ℂ)^2∈U)
include hU ha hAa hz hs hB hS he hup hBi hlam hphysical hb hBa hBi0 hSa hS0 hzeta0 hA0 hin

/-- The actual selected physical series inherits its first resonant amplitude. Every
finite competing order is discharged by the proved nonresonant or Vandermonde estimate. -/
theorem selectedPhysicalChartSeries_first_limit (n k : ℕ→ℕ) {p L j a : ℕ}
    (ha' : 0<a) (hpL : p<L) (hk : ∀i,k i≤n i+1)
    (henv : ∀C : ℝ,0≤C → Summable (fun i => hadamardEnvelope C (n i+1)))
    (hres : continuedRoot (b:ℂ)^(n p+1)=1)
    (hlower : ∀i<p,continuedRoot (b:ℂ)^(n i+1)≠1)
    (hhigher : ∀ i : ℕ, p < i → i < L → 1 ≤ n i ∧ 2*(j+1) ≤ (n i+1)*n i)
    (hbalance : n p+a+(n p+1)*n p=2*(j+1)) (hmajorant : Integrable (@shapeMajorant (n p) j))
    {G : ℕ→ℝ} (hG : Summable G)
    (htail : ∀ᶠ t : ℝ in 𝓝[>] 0,∀i,
      ‖iteratedDeriv j (fun v => A v*(spectralProduct lam (zeta v))^(k (i+L))*
        unscaledFullCoefficient (n (i+L)+1) lam (zeta v)) (Complex.I*(t:ℂ)^2)‖≤G i) :
    Tendsto (fun t : ℝ => (t^a) • iteratedDeriv j
      (selectedPhysicalChartSeries n k lam zeta A) (Complex.I*(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 ((A 0*(spectralProduct lam (zeta 0))^(k p))*edgeCoefficientLeading (n p) j b B S)) := by
  let f (i : ℕ) (v : ℂ) := A v*(spectralProduct lam (zeta v))^(k i)*
    unscaledFullCoefficient (n i+1) lam (zeta v)
  have htend : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((by fun_prop : Continuous (fun t : ℝ => Complex.I*(t:ℂ)^2)).tendsto 0).mono_left nhdsWithin_le_nhds
  have hg (i : ℕ) : AnalyticAt ℂ (fun v => A v*(spectralProduct lam (zeta v))^(k i)) 0 :=
    hA0.mul (((spectralProduct_analyticAt_ff lam (zeta 0)).comp hzeta0).pow (k i))
  apply scaled_series_first_limit ha' hpL (f := fun i t => iteratedDeriv j (f i) (Complex.I*(t:ℂ)^2))
  · filter_upwards [hin] with t ht
    exact selected_chart_series_hasSum_jets hU ha hAa hz (fun i => n i+1) k (fun _ => by omega) hk henv j ht
  · intro i hiL
    by_cases hip : i=p
    · subst i
      simp only [ite_true]
      exact weightedPhysicalCoefficient_first_leading_limit hU ha hz hs hB hS he hup hBi hlam hphysical
        ha' hbalance hmajorant hb hBa hBi0 hSa hS0 hres hin (hg p)
    · simp only [hip,ite_false]
      apply weightedPhysicalCoefficient_scaled_zero_of_bounds hU ha hz hs hB hS he hup hBi hlam hphysical ha' hin _ (hg i)
      intro r hrj
      rcases lt_or_gt_of_ne hip with hip'|hip'
      · obtain ⟨C,_,hc⟩ := edgeFullDerivativeIntegral_nonresonant_bounded hb hBa hBi0 hSa hS0 (hlower i hip') r
        exact ⟨C,htend.eventually hc⟩
      · obtain ⟨hni,hdegree⟩ := hhigher i hip' hiL
        obtain ⟨C,_,hc⟩ := edgeFullDerivativeIntegral_higher_bounded hni
          (by omega : 2*(r+1)≤(n i+1)*n i) hb hBa hBi0 hSa hS0
        exact ⟨C,hc⟩
  · exact hG
  · exact htail

end Chart
end
end IsingBulk.Anisotropic.RegularEdges
