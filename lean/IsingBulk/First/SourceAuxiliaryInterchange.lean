import IsingBulk.First.SourceAuxiliaryDomination

/-! Actual all-order parameter differentiation and angular/auxiliary Fubini.
The noncompact majorant is constructed at each fixed admissible radius and
parameter, before any boundary-uniform integration-by-parts estimate. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

theorem localizedDoubleAngleDensity_eq_auxiliary (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ)
    (J : Finset (SingularFactorIndex N)) (hJ : ∀ f ∈ J, validSourceFactor f)
    {s : ℂ} (hs : s ∈ dampingDomain r) (u : DoubleAngularVector N) :
    localizedDoubleAngleDensity r s w u =
      ∫ ξ : J → ℝ in positiveAuxiliaryOrthant J, sourceAuxiliaryDensity r w J s (u,ξ) := by
  simpa only [sourceAuxiliaryDensity, sourcePhaseSum, mul_comm] using
    localizedDoubleAngleDensity_exponential hN hr hr1 hs.2 w J hJ u

/-- This theorem includes genuine integrability of every full differentiated
angular/auxiliary density. The angular measure can be full Lebesgue measure or
its restriction to the original angle box. -/
theorem sourceAuxiliaryDensity_integrated_jets (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ)
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (J : Finset (SingularFactorIndex N)) (hJ : ∀ f ∈ J, validSourceFactor f)
    (μ : Measure (DoubleAngularVector N)) [SFinite μ] (hμ : μ ≤ volume)
    {s : ℂ} (hs : s ∈ dampingDomain r) (j : ℕ) :
    Integrable (fun p : DoubleAngularVector N × (J → ℝ) =>
      iteratedDeriv j (fun t => sourceAuxiliaryDensity r w J t p) s)
      (μ.prod (volume.restrict (positiveAuxiliaryOrthant J))) ∧
    iteratedDeriv j (fun t => ∫ u, localizedDoubleAngleDensity r t w u ∂μ) s =
      ∫ ξ : J → ℝ in positiveAuxiliaryOrthant J,
        ∫ u, iteratedDeriv j (fun t => sourceAuxiliaryDensity r w J t (u,ξ)) s ∂μ := by
  obtain ⟨U,hU,hsU,hUD,b,hb,hbound⟩ :=
    sourceAuxiliaryDensity_local_dominator N hN hr hr1 w hw hc J hJ hs
  have hμp : μ.prod (volume.restrict (positiveAuxiliaryOrthant J)) ≤
      volume.prod (volume.restrict (positiveAuxiliaryOrthant J)) := Measure.prod_mono hμ le_rfl
  have hb' := hb.mono_measure hμp
  have hbound' := Filter.Eventually.filter_mono (ae_mono hμp) hbound
  have hhol : ∀ p : DoubleAngularVector N × (J → ℝ), ∀ t ∈ U,
      AnalyticAt ℂ (fun z => sourceAuxiliaryDensity r w J z p) t :=
    fun p t ht => sourceAuxiliaryDensity_analyticAt N hN hr hr1 w J p (hUD ht)
  have hmeas : ∀ k t, t ∈ U → AEStronglyMeasurable
      (fun p : DoubleAngularVector N × (J → ℝ) =>
        iteratedDeriv k (fun z => sourceAuxiliaryDensity r w J z p) t)
      (μ.prod (volume.restrict (positiveAuxiliaryOrthant J))) := by
    intro k t ht
    exact (sourceAuxiliaryDensity_jet_continuous N hN hr hr1 w hw J hJ (hUD ht) k).aestronglyMeasurable
  have hi (k : ℕ) (t : ℂ) (ht : t ∈ U) :=
    (dominated_analytic_integral_jets (sourceAuxiliaryDensity r w J) hU hhol hmeas b hb' hbound' ht k).1
  have he : (fun t => ∫ u, localizedDoubleAngleDensity r t w u ∂μ) =ᶠ[𝓝 s]
      (fun t => ∫ p : DoubleAngularVector N × (J → ℝ), sourceAuxiliaryDensity r w J t p
        ∂μ.prod (volume.restrict (positiveAuxiliaryOrthant J))) := by
    filter_upwards [hU.mem_nhds hsU] with t ht
    have hit : Integrable (sourceAuxiliaryDensity r w J t)
        (μ.prod (volume.restrict (positiveAuxiliaryOrthant J))) := by
      simpa only [iteratedDeriv_zero] using hi 0 t ht
    rw [integral_prod _ hit]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall
      (fun u => localizedDoubleAngleDensity_eq_auxiliary N hN hr hr1 w J hJ (hUD ht) u)
  refine ⟨hi j s hsU, ?_⟩
  rw [he.iteratedDeriv_eq j,
    iteratedDeriv_integral_of_dominated_analytic (sourceAuxiliaryDensity r w J) hU hhol hmeas b hb' hbound' j hsU]
  exact integral_prod_symm _ (hi j s hsU)

/-- The original normalized localized contour object, its angle box and N!
are unchanged. All fixed-radius derivatives pass to the full source exponential
integrand and the actual auxiliary integral is genuinely convergent. -/
theorem localizedDoubleFormFactor_iteratedDeriv_auxiliary (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ)
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (J : Finset (SingularFactorIndex N)) (hJ : ∀ f ∈ J, validSourceFactor f)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) (j : ℕ) :
    iteratedDeriv j (fun t => localizedDoubleFormFactor N r t w) s =
      (N.factorial:ℂ)⁻¹ * ∫ ξ : J → ℝ in positiveAuxiliaryOrthant J,
        ∫ u in angleBox N ×ˢ angleBox N,
          iteratedDeriv j (fun t => sourceAuxiliaryDensity r w J t (u,ξ)) s := by
  have hh := sourceAuxiliaryDensity_integrated_jets N hN hr hr1 w hw hc J hJ
    (volume.restrict (angleBox N ×ˢ angleBox N)) Measure.restrict_le_self
    (dampingDomain_of_margin hr hr1 hm) j
  change iteratedDeriv j (fun t => (N.factorial:ℂ)⁻¹ *
    ∫ u in angleBox N ×ˢ angleBox N, localizedDoubleAngleDensity r t w u) s = _
  rw [iteratedDeriv_const_mul_field, hh.2]

end
end IsingBulk.First
