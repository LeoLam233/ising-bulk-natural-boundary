import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryJetsActual
import IsingBulk.Anisotropic.NegativeDominance.NegativeShiftedPeriod

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open Set Filter Metric MeasureTheory
open scoped Topology BigOperators

/-- The odd momentum constraint yields a genuine fixed-order boundary integral
and exact jets on its full torus, not only their inward limiting norms. -/
theorem odd_negative_whole_integral_analytic_jets (n : ℕ) (hn : Odd (n+1))
    {b : ℝ} {B S f : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0) :
    ∃a : ℝ,0<a ∧
      AnalyticOnNhd ℂ (fun u=>∫q : Fin n→ℝ,negativeShiftedFullIntegrand b B S n (f u) q
        ∂Measure.pi (fun _=>edgeAngleMeasure)) (ball 0 a) ∧
      (∀j u,‖u‖<a →
        Integrable (fun q : Fin n→ℝ=>iteratedDeriv j
          (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) u)
          (Measure.pi (fun _=>edgeAngleMeasure)) ∧
        iteratedDeriv j (fun w=>∫q : Fin n→ℝ,negativeShiftedFullIntegrand b B S n (f w) q
          ∂Measure.pi (fun _=>edgeAngleMeasure)) u =
          ∫q : Fin n→ℝ,iteratedDeriv j
            (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) u
            ∂Measure.pi (fun _=>edgeAngleMeasure)) := by
  obtain ⟨c,hc,hgap⟩ := odd_negative_boundary_product_gap hb hB
  let κ := c/((n+1:ℕ):ℝ)^2
  have hκ : 0<κ := by dsimp [κ]; positivity
  obtain ⟨a,ha,hdata⟩ := outerComplexQuotient_uniform_disk hb hB hBa hSa hS0 hf hf0 κ hκ
  have hμ : ∀ᵐ q : Fin n→ℝ ∂Measure.pi (fun _=>edgeAngleMeasure),
      q∈Icc (fun _=>-Real.pi) (fun _=>Real.pi) := by
    filter_upwards [edgeAngleMeasure_pi_ae_mem n] with q hq
    exact ⟨fun i=>(hq i).1,fun i=>(hq i).2⟩
  have hgap' (q : Fin n→ℝ) (_hq : q∈(univ : Set (Fin n→ℝ))) :
      κ≤‖1-edgeRootProduct b B 0 (negativeUnwrappedAngles n q)‖ := by
    have hh := hgap n hn q
    have ht := norm_sub_norm_le (1:ℂ) (∏i,edgeRoot b (B 0) (negativeShiftedAngles n q i))
    rw [norm_one] at ht
    have he := hh.trans ht
    simpa only [κ,negativeShiftedAngles,negativeUnwrappedAngles,edgeRootProduct,
      edgeParamRoot_zero,edgeRoot,edgeW,cos_wrapAngle] using he
  have hh := outer_gap_integral_jets_of_disk hb hB isCompact_Icc hμ MeasurableSet.univ
    (negativeUnwrappedAngles n) (negativeUnwrappedAngles_continuous n) (fun _=>1) continuous_const
    (div_pos ha (by positivity : (0:ℝ)<(n+1:ℕ))) hgap'
    (hdata (n+1) (by omega))
  refine ⟨a/((n+1:ℕ):ℝ),by positivity,?_⟩
  simpa only [negativeShiftedFullIntegrand_eq_unwrapped,one_mul,Measure.restrict_univ,integrableOn_univ] using hh

theorem odd_negativeShiftedPeriod_boundary_integral (n : ℕ) (hn : Odd (n+1))
    {b : ℝ} {B S f : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0) :
    AnalyticAt ℂ (fun u=>negativeShiftedPeriod b B S n (f u)) 0 ∧
      ∀j,iteratedDeriv j (fun u=>negativeShiftedPeriod b B S n (f u)) 0 =
        ((n+1).factorial:ℂ)⁻¹*(-1:ℂ)^((n+1).choose 2)*
          ∫q : Fin n→ℝ,iteratedDeriv j
            (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) 0
            ∂Measure.pi (fun _=>edgeAngleMeasure) := by
  obtain ⟨a,ha,hA,hj⟩ := odd_negative_whole_integral_analytic_jets n hn hb hB hBa hSa hS0 hf hf0
  constructor
  · exact analyticAt_const.mul (hA 0 (by simpa using ha))
  · intro j
    unfold negativeShiftedPeriod
    rw [iteratedDeriv_const_mul_field,(hj j 0 (by simpa using ha)).2]

end
end IsingBulk.Anisotropic.NegativeDominance
