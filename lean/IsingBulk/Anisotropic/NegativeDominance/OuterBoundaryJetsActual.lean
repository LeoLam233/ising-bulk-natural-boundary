import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryJetsIntegral
import IsingBulk.Anisotropic.NegativeDominance.OuterIntegralJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open Set Filter Metric MeasureTheory
open scoped Topology BigOperators

def negativeUnwrappedAngles (n : ℕ) (v : Fin n→ℝ) : Fin (n+1)→ℝ :=
  fun i=>physicalDependentAngles n (fun k=>v k+Real.pi) i-Real.pi

theorem negativeUnwrappedAngles_continuous (n : ℕ) : Continuous (negativeUnwrappedAngles n) := by
  unfold negativeUnwrappedAngles physicalDependentAngles
  fun_prop

theorem negativeShiftedFullIntegrand_eq_unwrapped (b : ℝ) (B S : ℂ→ℂ)
    (n : ℕ) (u : ℂ) (v : Fin n→ℝ) :
    negativeShiftedFullIntegrand b B S n u v=
      edgeFullIntegrand b B S u (negativeUnwrappedAngles n v) := by
  exact edgeFullIntegrand_wrapAngle b B S u (negativeUnwrappedAngles n v)

/-- Actual outer cutoff periods are holomorphic on a common particle-scale disk,
including its boundary center, and every derivative exchanges with integration. -/
theorem outer_negative_integral_analytic_jets {b : ℝ} {B S f : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hS0 : S 0≠0) (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0)
    (σ : ℝ) (hσ : 0<σ) :
    ∃a : ℝ,0<a ∧ ∀n : ℕ,∀E : Set (Fin n→ℝ),MeasurableSet E →
      (∀q∈E,σ≤∑i,(negativeShiftedAngles n q i)^2) →
      ∀χ : (Fin n→ℝ)→ℂ,Continuous χ →
      AnalyticOnNhd ℂ (fun u=>∫q in E,χ q*negativeShiftedFullIntegrand b B S n (f u) q
        ∂Measure.pi (fun _=>edgeAngleMeasure)) (ball 0 (a/((n+1:ℕ):ℝ))) ∧
      (∀j u,‖u‖<a/((n+1:ℕ):ℝ) →
        IntegrableOn (fun q=>χ q*iteratedDeriv j
          (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) u) E
          (Measure.pi (fun _=>edgeAngleMeasure)) ∧
        iteratedDeriv j (fun w=>∫q in E,χ q*negativeShiftedFullIntegrand b B S n (f w) q
          ∂Measure.pi (fun _=>edgeAngleMeasure)) u =
          ∫q in E,χ q*iteratedDeriv j
            (fun w=>negativeShiftedFullIntegrand b B S n (f w) q) u
            ∂Measure.pi (fun _=>edgeAngleMeasure)) := by
  obtain ⟨κ,hκ,hgap⟩ := outer_boundary_product_gap hb hB σ hσ
  obtain ⟨a,ha,hdata⟩ := outerComplexQuotient_uniform_disk hb hB hBa hSa hS0 hf hf0 κ hκ
  refine ⟨a,ha,?_⟩
  intro n E hE houter χ hχ
  have hμ : ∀ᵐ q : Fin n→ℝ ∂Measure.pi (fun _=>edgeAngleMeasure),
      q∈Icc (fun _=>-Real.pi) (fun _=>Real.pi) := by
    filter_upwards [edgeAngleMeasure_pi_ae_mem n] with q hq
    exact ⟨fun i=>(hq i).1,fun i=>(hq i).2⟩
  have hgap' (q : Fin n→ℝ) (hq : q∈E) :
      κ≤‖1-edgeRootProduct b B 0 (negativeUnwrappedAngles n q)‖ := by
    have hh := hgap (n+1) (negativeShiftedAngles n q)
      (fun i=>wrapAngle_mem _) (houter q hq)
    simpa only [negativeShiftedAngles,negativeUnwrappedAngles,edgeRootProduct,
      edgeParamRoot_zero,edgeRoot,edgeW,cos_wrapAngle] using hh
  have hh := outer_gap_integral_jets_of_disk hb hB isCompact_Icc hμ hE
    (negativeUnwrappedAngles n) (negativeUnwrappedAngles_continuous n) χ hχ
    (div_pos ha (by positivity : (0:ℝ)<(n+1:ℕ))) hgap'
    (hdata (n+1) (by omega))
  simpa only [negativeShiftedFullIntegrand_eq_unwrapped] using hh

end
end IsingBulk.Anisotropic.NegativeDominance
