import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryJetsWhole
import IsingBulk.Anisotropic.NegativeDominance.ComposedPeriodJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Filter MeasureTheory
open scoped Topology BigOperators

/-- Exact boundary integral for the genuinely continued, physically weighted
odd-particle coefficient in the manuscript parameter. -/
theorem scaled_negative_boundary_jet_integral
    {ι : Type*} {l : Filter ι} [NeBot l] {path : ι→ℂ}
    (n : ℕ) (hn : Odd (n+1)) {lam b : ℝ} {B S A zeta f : ℂ→ℂ} {U V : Set ℂ}
    (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hSzero : S 0≠0)
    (hAa : AnalyticAt ℂ A 0) (hA0 : A 0≠0) (hzeta : AnalyticAt ℂ zeta 0)
    (hSedge : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b:ℂ)*spectralS (zeta 0))
    (hBedge : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im)
    (hB : ∀u∈U,B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀u∈U,S u=spectralS (zeta u))
    (he : ∀u∈U,edgeMapV lam (-1) (zeta u)=(b:ℂ)+u)
    (hup : ∀u∈U,0<u.im) (hBi : ∀u∈U,0<(B u).im)
    (hV : IsOpen V) (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0) (hmap : MapsTo f V U)
    (hp : Tendsto path l (𝓝 0)) (hin : ∀ᶠt in l,path t∈V) (j : ℕ) :
    Integrable (fun q : Fin n→ℝ=>iteratedDeriv j
      (fun w=>negativeShiftedFullIntegrand b B (fun v=>S v/A v) n (f w) q) 0)
      (Measure.pi (fun _=>edgeAngleMeasure)) ∧
    iteratedDeriv j (fun t=>(A (f t))^(n+1)*continuedAngularCoefficient n lam (zeta (f t))) 0=
      ((n+1).factorial:ℂ)⁻¹*(-1:ℂ)^((n+1).choose 2)*
        ∫q : Fin n→ℝ,iteratedDeriv j
          (fun w=>negativeShiftedFullIntegrand b B (fun v=>S v/A v) n (f w) q) 0
          ∂Measure.pi (fun _=>edgeAngleMeasure) := by
  have hSdiv := hSa.div hAa hA0
  have hSdiv0 := div_ne_zero hSzero hA0
  obtain ⟨a,ha,_hwhole,hwholej⟩ :=
    odd_negative_whole_integral_analytic_jets n hn hb hB0 hBa hSdiv hSdiv0 hf hf0
  refine ⟨(hwholej j 0 (by simpa using ha)).1,?_⟩
  obtain ⟨hmodel,hmodelj⟩ :=
    odd_negativeShiftedPeriod_boundary_integral n hn hb hB0 hBa hSdiv hSdiv0 hf hf0
  have hG : AnalyticAt ℂ
      (fun t=>(A (f t))^(n+1)*continuedAngularCoefficient n lam (zeta (f t))) 0 :=
    (((hAa.pow (n+1)).mul
      ((continuedAngularCoefficient_negative_analyticAt n hn hSedge hedge hb hBedge).comp hzeta))).comp_of_eq hf hf0
  have hcG : ContinuousAt (iteratedDeriv j
      (fun t=>(A (f t))^(n+1)*continuedAngularCoefficient n lam (zeta (f t)))) 0 := by
    simpa only [iteratedDeriv_eq_iterate,Pi.div_def] using (hG.iterated_deriv j).continuousAt
  have hcM : ContinuousAt (iteratedDeriv j
      (fun t=>negativeShiftedPeriod b B (fun v=>S v/A v) n (f t))) 0 := by
    simpa only [iteratedDeriv_eq_iterate,Pi.div_def] using (hmodel.iterated_deriv j).continuousAt
  have hlim : Tendsto (fun t=>iteratedDeriv j
      (fun w=>negativeShiftedPeriod b B (fun v=>S v/A v) n (f w)) (path t)) l
      (𝓝 (iteratedDeriv j
        (fun t=>(A (f t))^(n+1)*continuedAngularCoefficient n lam (zeta (f t))) 0)) := by
    apply (hcG.tendsto.comp hp).congr'
    filter_upwards [hin] with t ht
    have hevent : (fun w=>negativeShiftedPeriod b B (fun v=>S v/A v) n (f w)) =ᶠ[𝓝 (path t)]
        (fun t=>(A (f t))^(n+1)*continuedAngularCoefficient n lam (zeta (f t))) := by
      filter_upwards [hV.mem_nhds ht] with w hw
      rw [negativeShiftedPeriod_div_scale,
        ←continuedAngularCoefficient_eq_negativeShiftedPeriod n (hB _ (hmap hw)) (hS _ (hmap hw))
          (he _ (hmap hw)) (hup _ (hmap hw)) (hBi _ (hmap hw))]
    exact (hevent.iteratedDeriv_eq j).symm
  exact (tendsto_nhds_unique hlim (hcM.tendsto.comp hp)).trans (hmodelj j)

/-- Exact measurable inner/outer partition of a genuine boundary Taylor integral. -/
theorem boundary_taylor_integral_partition {n j : ℕ} {b : ℝ} {B S f : ℂ→ℂ}
    {E : Set (Fin n→ℝ)} (hE : MeasurableSet E)
    (hi : Integrable (fun q : Fin n→ℝ=>iteratedDeriv j
      (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) 0)
      (Measure.pi (fun _=>edgeAngleMeasure))) :
    (∫q : Fin n→ℝ,iteratedDeriv j (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) 0 /
      (j.factorial:ℂ) ∂Measure.pi (fun _=>edgeAngleMeasure)) =
    (∫q in E,iteratedDeriv j (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) 0 /
      (j.factorial:ℂ) ∂Measure.pi (fun _=>edgeAngleMeasure)) +
    (∫q in Eᶜ,iteratedDeriv j (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) 0 /
      (j.factorial:ℂ) ∂Measure.pi (fun _=>edgeAngleMeasure)) := by
  exact (integral_add_compl hE (hi.div_const (j.factorial:ℂ))).symm

end
end IsingBulk.Anisotropic.NegativeDominance
