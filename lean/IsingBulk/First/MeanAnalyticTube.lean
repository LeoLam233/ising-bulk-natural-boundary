import IsingBulk.First.MeanSeparatedDerivativeBounds

/-! Actual regular parameter neighborhoods for the separated side/edge
integrals, in addition to their quantitative derivative bounds. -/
namespace IsingBulk.First
noncomputable section
open Set Filter Metric Complex
open scoped Topology

 theorem compact_analytic_parameter_domain
    {E P X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup P] [ProperSpace P] [TopologicalSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K) (F : ℂ × E → ℂ)
    (g : P × X → ℂ × E) (hg : Continuous g) (p₀ : P)
    (hbase : ∀ x ∈ K, AnalyticAt ℂ F (g (p₀,x))) :
    ∃ r : ℝ, 0 < r ∧ ∀ p : P, ‖p-p₀‖ ≤ r → ∀ x ∈ K, AnalyticAt ℂ F (g (p,x)) := by
  let U : Set (P × X) := g ⁻¹' {q | AnalyticAt ℂ F q}
  have hU : IsOpen U := (isOpen_analyticAt ℂ F).preimage hg
  have hsub : ({p₀} : Set P) ×ˢ K ⊆ U := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    have hp' : p=p₀ := mem_singleton_iff.mp hp
    subst p
    exact hbase x hx
  obtain ⟨V,W,hVo,_hWo,hpV,hKW,hVW⟩ := generalized_tube_lemma isCompact_singleton hK hU hsub
  have hVmem : V ∈ 𝓝 p₀ := hVo.mem_nhds (hpV (mem_singleton p₀))
  obtain ⟨eta,heta,hball⟩ := Metric.mem_nhds_iff.mp hVmem
  refine ⟨eta/2,half_pos heta,?_⟩
  intro p hp x hx
  apply hVW ⟨hball ?_,hKW hx⟩
  change dist p p₀ < eta
  rw [dist_eq_norm]
  linarith

/-- A fixed ordinary complex parameter neighborhood works uniformly on the
actual separated mean annulus. -/
theorem actual_mean_separated_analytic (a : OrderedChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ delta r : ℝ, 0 < delta ∧ 0 < r ∧
      ∀ (s : ℂ) (rho : ℝ) (t : Fin n → ℝ),
        ‖(s,rho,t)-(exp ((a.theta:ℂ)*I),0,0)‖ ≤ r →
        ∀ v ∈ meanSeparatedAnnulus delta, AnalyticAt ℂ (fun z => meanLocalDensity z rho a.alpha t v) s := by
  obtain ⟨delta,hd,hbase⟩ := actual_mean_separated_base_analytic a n halpha hbeta
  obtain ⟨r,hr,hreg⟩ := compact_analytic_parameter_domain (meanSeparatedAnnulus_compact delta)
    (complexMeanFullDensity a.alpha) (meanParameterPullback n) (meanParameterPullback_continuous n)
    (exp ((a.theta:ℂ)*I),0,0) hbase
  refine ⟨delta,r,hd,hr,?_⟩
  intro s rho t hp v hv
  have ha := hreg (s,rho,t) hp v hv
  change AnalyticAt ℂ (complexMeanFullDensity a.alpha) (s,meanComplexCoordinates rho t v) at ha
  have hs : AnalyticAt ℂ (fun z => complexMeanFullDensity a.alpha (z,meanComplexCoordinates rho t v)) s :=
    ha.comp (f := fun z : ℂ => (z,meanComplexCoordinates rho t v)) (analyticAt_id.prod analyticAt_const)
  exact hs.congr (Eventually.of_forall (fun z => complexMeanFullDensity_mean_coordinates z rho a.alpha t v))

end
end IsingBulk.First
