import IsingBulk.AnisoF002.C03.IsotropicPeriodicCurrentIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Actual parameter integrals and currents with a fixed null exceptional set

A common parameter neighborhood and an integrable first-derivative
majorant justify differentiation away from a fixed null angular set.
No derivative or C1 extension is required at the exceptional angles.
The box wrapper then integrates the genuine periodic angular current,
including any scalar radial chain-rule factor independent of angles.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter Metric MeasureTheory

section Measure
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Differentiation under the actual measure ignores the same null set
for every parameter in one fixed neighborhood. -/
theorem integral_hasDerivAt_off_null {F F' : ℝ → X → ℂ} {t : ℝ} {U : Set ℝ}
    {S : Set X} {B : X → ℝ} (hU : U ∈ 𝓝 t)
    (hS : ∀ᵐ x ∂μ, x ∉ S)
    (hFmeas : ∀ᶠ u in 𝓝 t, AEStronglyMeasurable (F u) μ)
    (hF0 : Integrable (F t) μ) (hDmeas : AEStronglyMeasurable (F' t) μ)
    (hB : Integrable B μ)
    (hbound : ∀ x, x ∉ S → ∀ u ∈ U, ‖F' u x‖ ≤ B x)
    (hderiv : ∀ x, x ∉ S → ∀ u ∈ U, HasDerivAt (fun v => F v x) (F' u x) u) :
    Integrable (F' t) μ ∧
      HasDerivAt (fun u : ℝ => ∫ x, F u x ∂μ) (∫ x, F' t x ∂μ) t := by
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hU hFmeas hF0 hDmeas
    (hS.mono fun x hx u hu => hbound x hx u hu) hB
    (hS.mono fun x hx u hu => hderiv x hx u hu)

variable [TopologicalSpace X] [OpensMeasurableSpace X]

theorem aestronglyMeasurable_of_continuousOn_ae_set {f : X → ℂ} {G : Set X}
    (hG : MeasurableSet G) (hμG : ∀ᵐ x ∂μ, x ∈ G) (hf : ContinuousOn f G) :
    AEStronglyMeasurable f μ := by
  have hh := hf.aestronglyMeasurable (μ := μ) hG
  rwa [Measure.restrict_eq_self_of_ae_mem hμG] at hh

/-- Bounded first jets on a finite measure support supply the full
integrability and measurability hypotheses. Continuity is required only
on the complement of the fixed exceptional set. -/
theorem integral_hasDerivAt_bounded_off_null [IsFiniteMeasure μ]
    {F F' : ℝ → X → ℂ} {t r M₀ M₁ : ℝ} {K S : Set X}
    (hr : 0 < r) (hK : MeasurableSet K) (hS : MeasurableSet S)
    (hμK : ∀ᵐ x ∂μ, x ∈ K) (hμS : ∀ᵐ x ∂μ, x ∉ S)
    (hF : ∀ u ∈ ball t r, ContinuousOn (F u) (K \ S))
    (hD : ContinuousOn (F' t) (K \ S))
    (hzero : ∀ x ∈ K \ S, ‖F t x‖ ≤ M₀)
    (hbound : ∀ x ∈ K \ S, ∀ u ∈ ball t r, ‖F' u x‖ ≤ M₁)
    (hderiv : ∀ x ∈ K \ S, ∀ u ∈ ball t r, HasDerivAt (fun v => F v x) (F' u x) u) :
    Integrable (F' t) μ ∧
      HasDerivAt (fun u : ℝ => ∫ x, F u x ∂μ) (∫ x, F' t x ∂μ) t := by
  have hG : MeasurableSet (K \ S) := hK.diff hS
  have hμG : ∀ᵐ x ∂μ, x ∈ K \ S := hμK.and hμS
  have hmeas (u : ℝ) (hu : u ∈ ball t r) : AEStronglyMeasurable (F u) μ :=
    aestronglyMeasurable_of_continuousOn_ae_set hG hμG (hF u hu)
  have hbase : Integrable (F t) μ :=
    (integrable_const M₀).mono' (hmeas t (mem_ball_self hr)) (hμG.mono fun x hx => hzero x hx)
  have hDmeas := aestronglyMeasurable_of_continuousOn_ae_set hG hμG hD
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := ball t r) (bound := fun _ => M₁) (ball_mem_nhds t hr)
  · filter_upwards [ball_mem_nhds t hr] with u hu
    exact hmeas u hu
  · exact hbase
  · exact hDmeas
  · exact hμG.mono fun x hx u hu => hbound x hx u hu
  · exact integrable_const M₁
  · exact hμG.mono fun x hx u hu => hderiv x hx u hu

end Measure

/-- Literal finite angular-box differentiation, allowing a countable
coincidence set with no assumed density derivative on that set. -/
theorem box_integral_hasDerivAt_off_countable {n : ℕ}
    (a b : Fin (n + 1) → ℝ) (S : Set (Fin (n + 1) → ℝ)) (hS : S.Countable)
    (F F' : ℝ → (Fin (n + 1) → ℝ) → ℂ) (t r M₀ M₁ : ℝ) (hr : 0 < r)
    (hF : ∀ u ∈ ball t r, ContinuousOn (F u) (Icc a b \ S))
    (hD : ContinuousOn (F' t) (Icc a b \ S))
    (hzero : ∀ x ∈ Icc a b \ S, ‖F t x‖ ≤ M₀)
    (hbound : ∀ x ∈ Icc a b \ S, ∀ u ∈ ball t r, ‖F' u x‖ ≤ M₁)
    (hderiv : ∀ x ∈ Icc a b \ S, ∀ u ∈ ball t r,
      HasDerivAt (fun v => F v x) (F' u x) u) :
    IntegrableOn (F' t) (Icc a b) volume ∧
      HasDerivAt (fun u : ℝ => ∫ x in Icc a b, F u x) (∫ x in Icc a b, F' t x) t := by
  let : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  exact integral_hasDerivAt_bounded_off_null (μ := volume.restrict (Icc a b)) hr
    measurableSet_Icc hS.measurableSet (ae_restrict_mem measurableSet_Icc)
    (hS.ae_notMem (volume.restrict (Icc a b))) hF hD hzero hbound hderiv

/-- The parameter derivative of the actual box integral is the next
current density, multiplied by the scalar radial chain-rule coefficient.
All angular flux terms cancel by the actual periodic face identity. -/
theorem box_current_hasDerivAt_off_countable {n : ℕ}
    (a b : Fin (n + 1) → ℝ) (hab : a ≤ b)
    (S : Set (Fin (n + 1) → ℝ)) (hS : S.Countable)
    (density densityDeriv : ℝ → (Fin (n + 1) → ℝ) → ℂ)
    (t r M₀ M₁ : ℝ) (hr : 0 < r)
    (hdensity : ∀ u ∈ ball t r, ContinuousOn (density u) (Icc a b \ S))
    (hderivCont : ContinuousOn (densityDeriv t) (Icc a b \ S))
    (hzero : ∀ x ∈ Icc a b \ S, ‖density t x‖ ≤ M₀)
    (hbound : ∀ x ∈ Icc a b \ S, ∀ u ∈ ball t r, ‖densityDeriv u x‖ ≤ M₁)
    (hderiv : ∀ x ∈ Icc a b \ S, ∀ u ∈ ball t r,
      HasDerivAt (fun v => density v x) (densityDeriv u x) u)
    (flux : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℂ)
    (fluxDeriv : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℂ)
    (hflux : ∀ i, ContinuousOn (flux i) (Icc a b))
    (hfluxDeriv : ∀ x ∈ (Set.univ.pi fun i => Ioo (a i) (b i)) \ S,
      ∀ i, HasFDerivAt (flux i) (fluxDeriv i x) x)
    (hfaces : ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      flux i (i.insertNth (b i) y) = flux i (i.insertNth (a i) y))
    (radialFactor : ℂ) (nextDensity : (Fin (n + 1) → ℝ) → ℂ)
    (hnext : IntegrableOn nextDensity (Icc a b) volume)
    (hcurrent : ∀ x ∈ Icc a b, x ∉ S →
      densityDeriv t x - (∑ i, fluxDeriv i x (Pi.single i 1)) = radialFactor * nextDensity x) :
    HasDerivAt (fun u : ℝ => ∫ x in Icc a b, density u x)
      (radialFactor * ∫ x in Icc a b, nextDensity x) t := by
  obtain ⟨hI, hparam⟩ := box_integral_hasDerivAt_off_countable a b S hS density densityDeriv
    t r M₀ M₁ hr hdensity hderivCont hzero hbound hderiv
  have he := integrated_current_off_countable a b hab flux fluxDeriv S hS hflux hfluxDeriv hfaces
    (densityDeriv t) (fun x => radialFactor * nextDensity x) hI (hnext.const_mul radialFactor) hcurrent
  rw [integral_const_mul] at he
  rwa [he] at hparam

end IsingBulk.AnisoF002.Isotropic
