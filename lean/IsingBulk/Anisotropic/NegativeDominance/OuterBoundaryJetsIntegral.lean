import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryJetsDisk

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set Filter Metric MeasureTheory
open scoped Topology BigOperators

/-- Restricted-measure exchange on the actual compact boundary-gap locus.
No regularity of the measurable outer partition itself is assumed. -/
theorem outer_gap_integral_jets_of_disk
    {m N : ℕ} {b : ℝ} {B S f : ℂ→ℂ} (hb : |b|<1) (hB : 0<(B 0).im)
    {μ : Measure (Fin m→ℝ)} [IsFiniteMeasure μ]
    {K₀ E : Set (Fin m→ℝ)} (hK₀ : IsCompact K₀) (hμ : ∀ᵐ x ∂μ,x∈K₀)
    (hE : MeasurableSet E) (Q : (Fin m→ℝ)→(Fin N→ℝ)) (hQ : Continuous Q)
    (χ : (Fin m→ℝ)→ℂ) (hχ : Continuous χ) {κ a : ℝ} (_ha : 0<a)
    (hgap : ∀x∈E,κ≤‖1-edgeRootProduct b B 0 (Q x)‖)
    (hdata : ∀q : Fin N→ℝ,κ≤‖1-edgeRootProduct b B 0 q‖ → ∀u : ℂ,‖u‖<a →
      AnalyticAt ℂ (@outerComplexQuotient N b B S f) (u,fun i=>(q i:ℂ)) ∧
      1-edgeRootProduct b B (f u) q≠0) :
    AnalyticOnNhd ℂ (fun u=>∫x in E,χ x*edgeFullIntegrand b B S (f u) (Q x) ∂μ) (ball 0 a) ∧
    (∀j u,‖u‖<a → IntegrableOn (fun x=>χ x*iteratedDeriv j
      (fun w=>edgeFullIntegrand b B S (f w) (Q x)) u) E μ ∧
      iteratedDeriv j (fun w=>∫x in E,χ x*edgeFullIntegrand b B S (f w) (Q x) ∂μ) u =
        ∫x in E,χ x*iteratedDeriv j (fun w=>edgeFullIntegrand b B S (f w) (Q x)) u ∂μ) := by
  let ν := μ.restrict E
  let K := K₀ ∩ {x | κ≤‖1-edgeRootProduct b B 0 (Q x)‖}
  have hp : Continuous (fun x=>edgeRootProduct b B 0 (Q x)) := by
    unfold edgeRootProduct
    apply continuous_finsetProd
    intro i _
    simpa only [edgeParamRoot_zero,Function.comp_def] using (edgeRoot_continuous hb hB).comp ((continuous_apply i).comp hQ)
  have hK : IsCompact K := hK₀.inter_right (isClosed_le continuous_const (continuous_const.sub hp).norm)
  have hν : ∀ᵐ x ∂ν,x∈K := by
    filter_upwards [ae_restrict_of_ae hμ,ae_restrict_mem hE] with x hx hxE
    exact ⟨hx,hgap x hxE⟩
  have hrK : ν.restrict K=ν := Measure.restrict_eq_self_of_ae_mem hν
  let ψ : (Fin m→ℝ)→(Fin N→ℂ) := fun x i=>(Q x i:ℂ)
  have hψ : Continuous ψ := by unfold ψ; fun_prop
  let c : (Fin m→ℝ)→ℂ := fun x=>(firstVandermonde (Q x):ℂ)^2*edgeSincFactor (Q x)
  have hc : Continuous c := by
    apply Continuous.mul
    · unfold firstVandermonde; fun_prop
    · exact (edgeSincFactor_continuous N).comp hQ
  let F := @outerComplexQuotient N b B S f
  let w : (Fin m→ℝ)→ℂ := fun x=>χ x*c x
  have hw : Continuous w := hχ.mul hc
  have hF : ∀u∈ball (0:ℂ) a,∀x∈K,AnalyticAt ℂ F (u,ψ x) := by
    intro u hu x hx
    exact (hdata (Q x) hx.2 u (by simpa using hu)).1
  let g : ℂ→ℂ := fun u=>∫x in K,w x*F (u,ψ x) ∂ν
  have hfactor (u : ℂ) (hu : ‖u‖<a) (x : Fin m→ℝ) (hx : x∈K) :
      edgeFullIntegrand b B S (f u) (Q x)=c x*F (u,ψ x) := by
    exact edgeFullIntegrand_eq_analytic_factor b B S (f u) (Q x) (hdata (Q x) hx.2 u hu).2
  have heq (u : ℂ) (hu : ‖u‖<a) :
      g u=∫x in E,χ x*edgeFullIntegrand b B S (f u) (Q x) ∂μ := by
    dsimp only [g]
    rw [hrK]
    apply integral_congr_ae
    filter_upwards [hν] with x hx
    rw [hfactor u hu x hx]
    simp only [w,mul_assoc]
  have heqEv (u : ℂ) (hu : ‖u‖<a) : g =ᶠ[𝓝 u]
      (fun w=>∫x in E,χ x*edgeFullIntegrand b B S (f w) (Q x) ∂μ) := by
    filter_upwards [isOpen_ball.mem_nhds (show u∈ball (0:ℂ) a by simpa using hu)] with z hz
    exact heq z (by simpa using hz)
  constructor
  · intro u hu
    exact (compact_analytic_shape_integral_analyticAt hK isOpen_ball F ψ hψ w hw hF hu).congr
      (heqEv u (by simpa using hu))
  · intro j u hu
    have hpjet (x : Fin m→ℝ) (hx : x∈K) : χ x*iteratedDeriv j
        (fun z=>edgeFullIntegrand b B S (f z) (Q x)) u =
        w x*iteratedDeriv j (fun z=>F (z,ψ x)) u := by
      have he : (fun z=>edgeFullIntegrand b B S (f z) (Q x)) =ᶠ[𝓝 u]
          (fun z=>c x*F (z,ψ x)) := by
        filter_upwards [isOpen_ball.mem_nhds (show u∈ball (0:ℂ) a by simpa using hu)] with z hz
        exact hfactor z (by simpa using hz) x hx
      rw [he.iteratedDeriv_eq j,iteratedDeriv_const_mul_field]
      simp only [w,mul_assoc]
    have hcont : ContinuousOn (fun x=>w x*iteratedDeriv j (fun z=>F (z,ψ x)) u) K := by
      intro x hx
      have hJ := (jointParameterJet_analyticAt (hF u (by simpa using hu) x hx) j).continuousAt
      have hcomp := hJ.comp (f := fun x=>(u,ψ x)) (continuous_const.prodMk hψ).continuousAt
      have hh := hw.continuousAt.mul hcomp
      simpa only [Pi.mul_def,Function.comp_def,jointParameterJet_eq,←iteratedDeriv_eq_iterate] using hh.continuousWithinAt
    have hint := hcont.integrableOn_compact (μ := ν) hK
    rw [IntegrableOn,hrK] at hint
    have hint' : IntegrableOn (fun x=>χ x*iteratedDeriv j
        (fun z=>edgeFullIntegrand b B S (f z) (Q x)) u) E μ := by
      apply hint.congr
      filter_upwards [hν] with x hx
      exact (hpjet x hx).symm
    refine ⟨hint',?_⟩
    rw [←(heqEv u hu).iteratedDeriv_eq j]
    have hj := compact_analytic_shape_integral_iteratedDeriv (μ := ν) hK isOpen_ball F ψ hψ w hw hF j u
      (show u∈ball (0:ℂ) a by simpa using hu)
    change iteratedDeriv j g u= _
    rw [show iteratedDeriv j g u=∫x in K,w x*iteratedDeriv j (fun z=>F (z,ψ x)) u ∂ν by
      simpa only [←iteratedDeriv_eq_iterate] using hj]
    rw [hrK]
    apply integral_congr_ae
    filter_upwards [hν] with x hx
    exact (hpjet x hx).symm

end
end IsingBulk.Anisotropic.NegativeDominance
