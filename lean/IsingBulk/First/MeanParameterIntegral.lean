import IsingBulk.First.MeanAnalyticTube
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Differentiation under the actual compact side and edge integrals. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

theorem compact_parameter_integral_hasDerivAt
    {K : Set ℝ} (hK : IsCompact K) {U : Set ℂ} (hU : IsOpen U)
    (H : ℕ → ℂ → ℝ → ℂ)
    (hc : ∀ j s, s ∈ U → ContinuousOn (H j s) K)
    (hd : ∀ j s, s ∈ U → ∀ x ∈ K, HasDerivAt (fun z => H j z x) (H (j+1) s x) s)
    (hb : ∀ j, ∃ C : ℝ, ∀ s ∈ U, ∀ x ∈ K, ‖H j s x‖ ≤ C)
    (j : ℕ) (s : ℂ) (hs : s ∈ U) :
    HasDerivAt (fun z => ∫ x in K, H j z x) (∫ x in K, H (j+1) s x) s := by
  obtain ⟨C,hC⟩ := hb (j+1)
  have hm (i : ℕ) (z : ℂ) (hz : z ∈ U) : Integrable (H i z) (volume.restrict K) :=
    (hc i z hz).integrableOn_compact hK
  have hbound : Integrable (fun _ : ℝ => C) (volume.restrict K) :=
    (continuousOn_const.integrableOn_compact hK)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (hU.mem_nhds hs)
    ((show ∀ᶠ z in 𝓝 s, z ∈ U from hU.mem_nhds hs).mono fun z hz => (hm j z hz).aestronglyMeasurable)
    (hm j s hs) (hm (j+1) s hs).aestronglyMeasurable
    ((ae_restrict_mem hK.measurableSet).mono fun x hx z hz => hC z hz x hx)
    hbound
    ((ae_restrict_mem hK.measurableSet).mono fun x hx z hz => hd j z hz x hx)).2

/-- Every derivative is the integral of the corresponding literal derivative,
on the same open parameter domain. -/
theorem compact_parameter_integral_iteratedDeriv
    {K : Set ℝ} (hK : IsCompact K) {U : Set ℂ} (hU : IsOpen U)
    (H : ℕ → ℂ → ℝ → ℂ)
    (hc : ∀ j s, s ∈ U → ContinuousOn (H j s) K)
    (hd : ∀ j s, s ∈ U → ∀ x ∈ K, HasDerivAt (fun z => H j z x) (H (j+1) s x) s)
    (hb : ∀ j, ∃ C : ℝ, ∀ s ∈ U, ∀ x ∈ K, ‖H j s x‖ ≤ C)
    (j : ℕ) : ∀ s ∈ U,
    (deriv^[j] (fun z => ∫ x in K, H 0 z x)) s = ∫ x in K, H j s x := by
  induction j with
  | zero => intro s hs; rfl
  | succ j ih =>
    intro s hs
    rw [Function.iterate_succ',Function.comp_apply]
    have he : (deriv^[j] (fun z => ∫ x in K, H 0 z x)) =ᶠ[𝓝 s]
        (fun z => ∫ x in K, H j z x) := (show ∀ᶠ z in 𝓝 s, z ∈ U from hU.mem_nhds hs).mono fun z hz => ih z hz
    rw [he.deriv_eq]
    exact (compact_parameter_integral_hasDerivAt hK hU H hc hd hb j s hs).deriv

end
end IsingBulk.First
