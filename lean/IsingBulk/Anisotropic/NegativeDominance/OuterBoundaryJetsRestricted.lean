import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryJetsPaper

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open Set Filter Metric MeasureTheory
open scoped Topology BigOperators

/-- A single genuine paper-coordinate analytic disk works for every measurable
angular subset. The restriction is in the measure, not in an assumed exchange. -/
theorem paper_restricted_boundary_jets (n : ℕ) (hn : Odd (n+1))
    {lam b : ℝ} {zeta A : ℂ→ℂ} (hzeta : AnalyticAt ℂ zeta 0) (hA : AnalyticAt ℂ A 0)
    (hS : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b:ℂ)*spectralS (zeta 0))
    (hb : |b|<1) (hB : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im) :
    ∃r : ℝ,0<r ∧ ∀E : Set (Fin n→ℝ),E⊆Icc (fun _=>-Real.pi) (fun _=>Real.pi) →
      AnalyticOnNhd ℂ (fun t=>∫v in E,paperShiftedDensity n lam zeta A t v) (ball 0 r) ∧
      ∀j t,‖t‖<r →
      IntegrableOn (fun v : Fin n→ℝ=>iteratedDeriv j
        (fun t=>paperShiftedDensity n lam zeta A t v) t/(j.factorial:ℂ)) E ∧
      iteratedDeriv j (fun t=>∫v in E,paperShiftedDensity n lam zeta A t v) t/(j.factorial:ℂ)=
        ∫v in E,iteratedDeriv j (fun t=>paperShiftedDensity n lam zeta A t v) t/(j.factorial:ℂ) := by
  let K : Set (Fin n→ℝ) := Icc (fun _=>-Real.pi) (fun _=>Real.pi)
  let Q : (Fin n→ℝ)→(Fin (n+1)→ℝ) := fun v=>physicalDependentAngles n (fun k=>v k+Real.pi)
  have hQ : Continuous Q := (physicalDependentAngles_continuous n).comp
    (continuous_pi (fun k=>(continuous_apply k).add continuous_const))
  let ψ : (Fin n→ℝ)→(Fin (n+1)→ℂ) := fun v i=>(Q v i:ℂ)
  have hψ : Continuous ψ := by unfold ψ; fun_prop
  let C : ℂ := ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n
  let F : ℂ×(Fin (n+1)→ℂ)→ℂ := fun p=>C*(A p.1)^(n+1)*continuedAngularDensity lam (zeta p.1) p.2
  have hF0 (v : Fin n→ℝ) : AnalyticAt ℂ F (0,ψ v) := by
    have hd := continuedAngularDensity_negative_joint_analyticAt hn hS hedge hb hB
      (Q v) (physicalDependentAngles_sum_zero n (fun k=>v k+Real.pi))
    have hm : AnalyticAt ℂ (fun p : ℂ×(Fin (n+1)→ℂ)=>(zeta p.1,p.2)) (0,ψ v) :=
      (hzeta.comp (f := fun p : ℂ×(Fin (n+1)→ℂ)=>p.1) (x := (0,ψ v)) analyticAt_fst).prod analyticAt_snd
    have hdc := hd.comp (f := fun p : ℂ×(Fin (n+1)→ℂ)=>(zeta p.1,p.2)) (x := (0,ψ v)) hm
    exact (analyticAt_const.mul ((hA.comp (f := Prod.fst) analyticAt_fst).pow (n+1))).mul hdc
  have hev : ∀ᶠ t in 𝓝 (0:ℂ),∀v∈K,AnalyticAt ℂ F (t,ψ v) := by
    apply (isCompact_Icc : IsCompact K).eventually_forall_of_forall_eventually
    intro v _
    have hc : Continuous (fun p : ℂ×(Fin n→ℝ)=>(p.1,ψ p.2)) :=
      continuous_fst.prodMk (hψ.comp continuous_snd)
    exact hc.continuousAt.eventually (hF0 v).eventually_analyticAt
  obtain ⟨U,hU,hUopen,h0U⟩ := _root_.mem_nhds_iff.mp hev
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds h0U)
  refine ⟨r,hr,?_⟩
  intro E hEK
  let μ := volume.restrict E
  have hres : μ.restrict K=volume.restrict E := by
    rw [Measure.restrict_restrict (isCompact_Icc : IsCompact K).measurableSet,
      inter_eq_right.mpr hEK]
  have hF : ∀t∈ball (0:ℂ) r,∀v∈K,AnalyticAt ℂ F (t,ψ v) :=
    fun t ht v hv=>hU (hrU ht) v hv
  constructor
  · intro t ht
    have hh := compact_analytic_shape_integral_analyticAt (μ := μ) (K := K)
      isCompact_Icc isOpen_ball F ψ hψ (fun _=>1) continuous_const hF ht
    simpa only [one_mul,hres,F,ψ,Q,C,paperShiftedDensity] using hh
  · intro j t ht
    have hcont : ContinuousOn (fun v : Fin n→ℝ=>iteratedDeriv j
        (fun t=>paperShiftedDensity n lam zeta A t v) t) K := by
      intro v hv
      have hc := (jointParameterJet_analyticAt (hF t (by simpa using ht) v hv) j).continuousAt.comp
        (f := fun v=>(t,ψ v)) (continuous_const.prodMk hψ).continuousAt
      simpa only [Function.comp_def,jointParameterJet_eq,←iteratedDeriv_eq_iterate,F,ψ,Q,C,paperShiftedDensity]
        using hc.continuousWithinAt
    have hi := (hcont.integrableOn_compact (μ := μ) isCompact_Icc).div_const (j.factorial:ℂ)
    have hi' : IntegrableOn (fun v : Fin n→ℝ=>iteratedDeriv j
        (fun t=>paperShiftedDensity n lam zeta A t v) t/(j.factorial:ℂ)) E := by
      change Integrable _ (μ.restrict K) at hi
      rwa [hres] at hi
    refine ⟨hi',?_⟩
    have hj := compact_analytic_shape_integral_iteratedDeriv (μ := μ)
      (K := K) isCompact_Icc isOpen_ball F ψ hψ (fun _=>1) continuous_const hF j t
      (by simpa using ht)
    simp only [one_mul,←iteratedDeriv_eq_iterate,hres] at hj
    rw [integral_div]
    simpa only [F,ψ,Q,C,paperShiftedDensity] using congrArg (fun z : ℂ=>z/(j.factorial:ℂ)) hj

end
end IsingBulk.Anisotropic.NegativeDominance
