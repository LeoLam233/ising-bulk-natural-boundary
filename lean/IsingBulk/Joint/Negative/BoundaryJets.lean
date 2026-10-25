import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryJetsWhole
import IsingBulk.Joint.Negative.AngularDensity

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic.NegativeDominance
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open Set Filter Metric MeasureTheory
open scoped Topology BigOperators

/-- Literal paper-coordinate density on the translated centered Lebesgue cube. -/
def paperShiftedDensity (n : ℕ) (curve : ℂ→Coupling) (amp : ℂ→ℂ) (t : ℂ) (v : Fin n→ℝ) : ℂ :=
  (((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n)*(amp t)^(n+1)*
    continuedAngularDensity (curve t)
      (fun i=>(physicalDependentAngles n (fun k=>v k+Real.pi) i:ℂ))

theorem paperShiftedDensity_integral (n : ℕ) (curve : ℂ→Coupling) (amp : ℂ→ℂ) (t : ℂ) :
    (∫v in Icc (fun _=>-Real.pi) (fun _=>Real.pi),paperShiftedDensity n curve amp t v)=
      (amp t)^(n+1)*continuedAngularCoefficient n (curve t) := by
  unfold paperShiftedDensity continuedAngularCoefficient
  rw [angleBox_integral_eq_negative_shifted,integral_const_mul]
  ring

/-- Direct paper-chart boundary Taylor identity. Only actual negative-edge
joint analyticity and compact integration are used; no inward path, auxiliary
edge parameter, or derivative-exchange premise is needed. -/
theorem paper_weighted_boundary_taylor_integral (n : ℕ) (hn : Odd (n+1))
    {b : ℝ} {curve : ℂ→Coupling} {amp : ℂ→ℂ} (hcurve : AnalyticAt ℂ curve 0) (hA : AnalyticAt ℂ amp 0)
    (hS : S (curve 0)≠0)
    (hedge : A (curve 0)+T (curve 0)=(b:ℂ)*S (curve 0))
    (hb : |b|<1) (hB : 0<(-T (curve 0)/S (curve 0)).im) (j : ℕ) :
    IntegrableOn (fun v : Fin n→ℝ=>iteratedDeriv j (fun t=>paperShiftedDensity n curve amp t v) 0 /
      (j.factorial:ℂ)) (Icc (fun _=>-Real.pi) (fun _=>Real.pi)) ∧
    iteratedDeriv j (fun t=>(amp t)^(n+1)*continuedAngularCoefficient n (curve t)) 0 /
      (j.factorial:ℂ) =
      ∫v in Icc (fun _=>-Real.pi) (fun _=>Real.pi),
        iteratedDeriv j (fun t=>paperShiftedDensity n curve amp t v) 0/(j.factorial:ℂ) := by
  let K : Set (Fin n→ℝ) := Icc (fun _=>-Real.pi) (fun _=>Real.pi)
  let Q : (Fin n→ℝ)→(Fin (n+1)→ℝ) := fun v=>physicalDependentAngles n (fun k=>v k+Real.pi)
  have hQ : Continuous Q := (physicalDependentAngles_continuous n).comp
    (continuous_pi (fun k=>(continuous_apply k).add continuous_const))
  let ψ : (Fin n→ℝ)→(Fin (n+1)→ℂ) := fun v i=>(Q v i:ℂ)
  have hψ : Continuous ψ := by unfold ψ; fun_prop
  let C : ℂ := ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n
  let F : ℂ×(Fin (n+1)→ℂ)→ℂ := fun p=>C*(amp p.1)^(n+1)*continuedAngularDensity (curve p.1) p.2
  have hF0 (v : Fin n→ℝ) : AnalyticAt ℂ F (0,ψ v) := by
    have hd := continuedAngularDensity_negative_joint_analyticAt hn hS hedge hb hB
      (Q v) (physicalDependentAngles_sum_zero n (fun k=>v k+Real.pi))
    have hm : AnalyticAt ℂ (fun p : ℂ×(Fin (n+1)→ℂ)=>(curve p.1,p.2)) (0,ψ v) :=
      (hcurve.comp (f := fun p : ℂ×(Fin (n+1)→ℂ)=>p.1) (x := (0,ψ v)) analyticAt_fst).prod analyticAt_snd
    have hdc := hd.comp (f := fun p : ℂ×(Fin (n+1)→ℂ)=>(curve p.1,p.2)) (x := (0,ψ v)) hm
    exact (analyticAt_const.mul ((hA.comp (f := Prod.fst) analyticAt_fst).pow (n+1))).mul hdc
  have hev : ∀ᶠ t in 𝓝 (0:ℂ),∀v∈K,AnalyticAt ℂ F (t,ψ v) := by
    apply (isCompact_Icc : IsCompact K).eventually_forall_of_forall_eventually
    intro v _
    have hc : Continuous (fun p : ℂ×(Fin n→ℝ)=>(p.1,ψ p.2)) :=
      continuous_fst.prodMk (hψ.comp continuous_snd)
    exact hc.continuousAt.eventually (hF0 v).eventually_analyticAt
  obtain ⟨U,hU,hUopen,h0U⟩ := _root_.mem_nhds_iff.mp hev
  have hcont : ContinuousOn (fun v : Fin n→ℝ=>iteratedDeriv j
      (fun t=>paperShiftedDensity n curve amp t v) 0) K := by
    intro v _
    have hc := (jointParameterJet_analyticAt (hF0 v) j).continuousAt.comp
      (f := fun v=>((0:ℂ),ψ v)) (continuous_const.prodMk hψ).continuousAt
    simpa only [Function.comp_def,jointParameterJet_eq,←iteratedDeriv_eq_iterate,F,ψ,Q,C,paperShiftedDensity]
      using hc.continuousWithinAt
  refine ⟨(hcont.integrableOn_compact (μ := volume) isCompact_Icc).div_const _,?_⟩
  have hj := compact_analytic_shape_integral_iteratedDeriv (μ := volume)
    (K := K) isCompact_Icc hUopen F ψ hψ (fun _=>1) continuous_const
    (fun t ht v hv=>hU ht v hv) j 0 h0U
  have he : (fun t=>∫v in K,F (t,ψ v))=
      (fun t=>(amp t)^(n+1)*continuedAngularCoefficient n (curve t)) := by
    funext t
    exact paperShiftedDensity_integral n curve amp t
  simp only [one_mul,←iteratedDeriv_eq_iterate] at hj
  rw [he] at hj
  rw [hj,←integral_div]
  rfl

end
end IsingBulk.Joint.Negative
