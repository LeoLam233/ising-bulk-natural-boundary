import IsingBulk.First.OnsiteLocalizationAlgebra

/-! Actual finite localization and fixed-radius derivative linearity for the
onsite observable, with genuine integrability and holomorphy proved. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff

theorem localizedOnsiteAngleDensity_continuous (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (w : DoubleAngularVector N → ℝ) (hw : Continuous w) :
    Continuous (localizedOnsiteAngleDensity r s w) := by
  have hd := (normalizationDensities_continuous_angles N hN r s (globalRoot s)
    (globalRoot_admissible hr hr1 hm)).1
  have hb := doubleAngularDensityOf_continuous N r (onsiteDensity s) hd
  convert (Complex.continuous_ofReal.comp hw).mul hb using 1
  funext u
  simp only [localizedOnsiteAngleDensity,Pi.mul_apply,Function.comp_apply,doubleAngularDensityOf,mul_assoc]

theorem localizedOnsiteFormFactor_sum {ι : Type*} (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (I : Finset ι) (w : ι → DoubleAngularVector N → ℝ) (hw : ∀ i ∈ I, Continuous (w i)) :
    localizedOnsiteFormFactor N r s (fun u => ∑ i ∈ I, w i u) =
      ∑ i ∈ I, localizedOnsiteFormFactor N r s (w i) := by
  have hi (i) (hi : i ∈ I) : IntegrableOn (localizedOnsiteAngleDensity r s (w i))
      (angleBox N ×ˢ angleBox N) :=
    (localizedOnsiteAngleDensity_continuous N hN hr hr1 hm (w i) (hw i hi)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have he : localizedOnsiteAngleDensity r s (fun u => ∑ i ∈ I, w i u) =
      fun u => ∑ i ∈ I, localizedOnsiteAngleDensity r s (w i) u := by
    funext u
    unfold localizedOnsiteAngleDensity
    push_cast
    simp only [Finset.sum_mul]
  unfold localizedOnsiteFormFactor
  rw [he, integral_finsetSum I hi, Finset.mul_sum]

theorem localizedOnsiteFormFactor_iteratedDeriv_sum {ι : Type*} (N : ℕ) (hN : 0 < N) (j : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (I : Finset ι) (w : ι → DoubleAngularVector N → ℝ) (hw : ∀ i ∈ I, Continuous (w i)) :
    iteratedDeriv j (fun t => localizedOnsiteFormFactor N r t (fun u => ∑ i ∈ I, w i u)) s =
      ∑ i ∈ I, iteratedDeriv j (fun t => localizedOnsiteFormFactor N r t (w i)) s := by
  have he : (fun t => localizedOnsiteFormFactor N r t (fun u => ∑ i ∈ I, w i u)) =ᶠ[𝓝 s]
      (fun t => ∑ i ∈ I, localizedOnsiteFormFactor N r t (w i)) := by
    filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin hr hr1 hm)] with t ht
    exact localizedOnsiteFormFactor_sum N hN hr hr1 ht.2 I w hw
  rw [he.iteratedDeriv_eq j]
  exact iteratedDeriv_fun_sum (fun i hi =>
    (localizedOnsiteFormFactor_analyticAt N hN hr hr1 hm (w i) (hw i hi)).contDiffAt)

end
end IsingBulk.First
