import IsingBulk.First.OnsiteAuxiliaryDomination

/-! Actual all-order parameter differentiation and angular/auxiliary Fubini.
The noncompact majorant is constructed at each fixed admissible radius and
parameter, before any boundary-uniform integration-by-parts estimate. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

def localizedOnsiteFormFactor (N : ℕ) (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) : ℂ :=
  (N.factorial : ℂ)⁻¹ * ∫ u in angleBox N ×ˢ angleBox N, localizedOnsiteAngleDensity r s w u

theorem localizedOnsiteAngleDensity_exponential {N : ℕ} (hN : 0 < N) {r : ℝ} {s : ℂ}
    (hr : 0 < r) (hr1 : r < 1) (hmargin : r⁻¹-r < (sourceS s).im)
    (w : DoubleAngularVector N → ℝ)
    (J : Finset (SingularFactorIndex N)) (hJ : ∀ f ∈ J, isOnsiteFactor f ∧ validSourceFactor f)
    (u : DoubleAngularVector N) :
    localizedOnsiteAngleDensity r s w u =
      ∫ ξ : J → ℝ in positiveAuxiliaryOrthant J,
        onsiteRegularAmplitude r s w J u * Complex.exp
          (∑ f : J, sourceAngularExponent r s (fun _ => 1) (fun _ => 1) f.val u * (ξ f : ℂ)) := by
  rw [localizedOnsiteAngleDensity_factorization r s w J hJ, integral_const_mul]
  have hd (f : J) : (sourceAngularExponent r s (fun _ => 1) (fun _ => 1) f.val u).re < 0 :=
    singularFactorExponent_re_negative hN hr hr1 hmargin _ _ (by simp) (by simp) u f.val 1
  rw [integral_auxiliary_exponential _ hd]
  congr 1
  exact (Finset.prod_finset_coe (fun f : SingularFactorIndex N =>
    (-sourceAngularExponent r s (fun _ => 1) (fun _ => 1) f u)⁻¹) J).symm

theorem localizedOnsiteAngleDensity_eq_auxiliary (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ)
    (J : Finset (SingularFactorIndex N)) (hJ : ∀ f ∈ J, isOnsiteFactor f ∧ validSourceFactor f)
    {s : ℂ} (hs : s ∈ dampingDomain r) (u : DoubleAngularVector N) :
    localizedOnsiteAngleDensity r s w u =
      ∫ ξ : J → ℝ in positiveAuxiliaryOrthant J, onsiteAuxiliaryDensity r w J s (u,ξ) := by
  simpa only [onsiteAuxiliaryDensity, sourcePhaseSum, mul_comm] using
    localizedOnsiteAngleDensity_exponential hN hr hr1 hs.2 w J hJ u

/-- This theorem includes genuine integrability of every full differentiated
angular/auxiliary density. The angular measure can be full Lebesgue measure or
its restriction to the original angle box. -/
theorem onsiteAuxiliaryDensity_integrated_jets (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ)
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (J : Finset (SingularFactorIndex N)) (hJ : ∀ f ∈ J, isOnsiteFactor f ∧ validSourceFactor f)
    (μ : Measure (DoubleAngularVector N)) [SFinite μ] (hμ : μ ≤ volume)
    {s : ℂ} (hs : s ∈ dampingDomain r) (j : ℕ) :
    Integrable (fun p : DoubleAngularVector N × (J → ℝ) =>
      iteratedDeriv j (fun t => onsiteAuxiliaryDensity r w J t p) s)
      (μ.prod (volume.restrict (positiveAuxiliaryOrthant J))) ∧
    iteratedDeriv j (fun t => ∫ u, localizedOnsiteAngleDensity r t w u ∂μ) s =
      ∫ ξ : J → ℝ in positiveAuxiliaryOrthant J,
        ∫ u, iteratedDeriv j (fun t => onsiteAuxiliaryDensity r w J t (u,ξ)) s ∂μ := by
  obtain ⟨U,hU,hsU,hUD,b,hb,hbound⟩ :=
    onsiteAuxiliaryDensity_local_dominator N hN hr hr1 w hw hc J (fun f hf => (hJ f hf).2) hs
  have hμp : μ.prod (volume.restrict (positiveAuxiliaryOrthant J)) ≤
      volume.prod (volume.restrict (positiveAuxiliaryOrthant J)) := Measure.prod_mono hμ le_rfl
  have hb' := hb.mono_measure hμp
  have hbound' := Filter.Eventually.filter_mono (ae_mono hμp) hbound
  have hhol : ∀ p : DoubleAngularVector N × (J → ℝ), ∀ t ∈ U,
      AnalyticAt ℂ (fun z => onsiteAuxiliaryDensity r w J z p) t :=
    fun p t ht => onsiteAuxiliaryDensity_analyticAt N hN hr hr1 w J p (hUD ht)
  have hmeas : ∀ k t, t ∈ U → AEStronglyMeasurable
      (fun p : DoubleAngularVector N × (J → ℝ) =>
        iteratedDeriv k (fun z => onsiteAuxiliaryDensity r w J z p) t)
      (μ.prod (volume.restrict (positiveAuxiliaryOrthant J))) := by
    intro k t ht
    exact (onsiteAuxiliaryDensity_jet_continuous N hN hr hr1 w hw J (fun f hf => (hJ f hf).2) (hUD ht) k).aestronglyMeasurable
  have hi (k : ℕ) (t : ℂ) (ht : t ∈ U) :=
    (dominated_analytic_integral_jets (onsiteAuxiliaryDensity r w J) hU hhol hmeas b hb' hbound' ht k).1
  have he : (fun t => ∫ u, localizedOnsiteAngleDensity r t w u ∂μ) =ᶠ[𝓝 s]
      (fun t => ∫ p : DoubleAngularVector N × (J → ℝ), onsiteAuxiliaryDensity r w J t p
        ∂μ.prod (volume.restrict (positiveAuxiliaryOrthant J))) := by
    filter_upwards [hU.mem_nhds hsU] with t ht
    have hit : Integrable (onsiteAuxiliaryDensity r w J t)
        (μ.prod (volume.restrict (positiveAuxiliaryOrthant J))) := by
      simpa only [iteratedDeriv_zero] using hi 0 t ht
    rw [integral_prod _ hit]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall
      (fun u => localizedOnsiteAngleDensity_eq_auxiliary N hN hr hr1 w J hJ (hUD ht) u)
  refine ⟨hi j s hsU, ?_⟩
  rw [he.iteratedDeriv_eq j,
    iteratedDeriv_integral_of_dominated_analytic (onsiteAuxiliaryDensity r w J) hU hhol hmeas b hb' hbound' j hsU]
  exact integral_prod_symm _ (hi j s hsU)

/-- The original normalized localized contour object, its angle box and N!
are unchanged. All fixed-radius derivatives pass to the full source exponential
integrand and the actual auxiliary integral is genuinely convergent. -/
theorem localizedOnsiteFormFactor_iteratedDeriv_auxiliary (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (w : DoubleAngularVector N → ℝ)
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (J : Finset (SingularFactorIndex N)) (hJ : ∀ f ∈ J, isOnsiteFactor f ∧ validSourceFactor f)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) (j : ℕ) :
    iteratedDeriv j (fun t => localizedOnsiteFormFactor N r t w) s =
      (N.factorial:ℂ)⁻¹ * ∫ ξ : J → ℝ in positiveAuxiliaryOrthant J,
        ∫ u in angleBox N ×ˢ angleBox N,
          iteratedDeriv j (fun t => onsiteAuxiliaryDensity r w J t (u,ξ)) s := by
  have hh := onsiteAuxiliaryDensity_integrated_jets N hN hr hr1 w hw hc J hJ
    (volume.restrict (angleBox N ×ˢ angleBox N)) Measure.restrict_le_self
    (dampingDomain_of_margin hr hr1 hm) j
  change iteratedDeriv j (fun t => (N.factorial:ℂ)⁻¹ *
    ∫ u in angleBox N ×ˢ angleBox N, localizedOnsiteAngleDensity r t w u) s = _
  rw [iteratedDeriv_const_mul_field, hh.2]

end
end IsingBulk.First
