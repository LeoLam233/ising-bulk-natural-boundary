import IsingBulk.First.LocalizedAnalytic
import IsingBulk.First.NormalizationIntegral

/-! Actual finite localization and fixed-radius derivative linearity for the
offsite observable, with genuine integrability and holomorphy proved. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff

theorem localizedDoubleAngleDensity_continuous_damping (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (w : DoubleAngularVector N → ℝ) (hw : Continuous w) :
    Continuous (localizedDoubleAngleDensity r s w) := by
  have hroot := globalRoot_admissible hr hr1 hm
  have hd := doubleDensity_continuous_angles N hN r s (globalRoot s)
    (fun θ => hroot.toTuple N _ (fun _ => anglePoint_norm hr.le _))
  have hb := doubleAngularDensityOf_continuous N r (doubleDensity s) hd
  convert (Complex.continuous_ofReal.comp hw).mul hb using 1
  funext u
  simp only [localizedDoubleAngleDensity,Pi.mul_apply,Function.comp_apply,doubleAngularDensityOf,mul_assoc]

theorem localizedDoubleFormFactor_sum {ι : Type*} (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (I : Finset ι) (w : ι → DoubleAngularVector N → ℝ) (hw : ∀ i ∈ I, Continuous (w i)) :
    localizedDoubleFormFactor N r s (fun u => ∑ i ∈ I, w i u) =
      ∑ i ∈ I, localizedDoubleFormFactor N r s (w i) := by
  have hi (i) (hi : i ∈ I) : IntegrableOn (localizedDoubleAngleDensity r s (w i))
      (angleBox N ×ˢ angleBox N) :=
    (localizedDoubleAngleDensity_continuous_damping N hN hr hr1 hm (w i) (hw i hi)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have he : localizedDoubleAngleDensity r s (fun u => ∑ i ∈ I, w i u) =
      fun u => ∑ i ∈ I, localizedDoubleAngleDensity r s (w i) u := by
    funext u
    unfold localizedDoubleAngleDensity
    push_cast
    simp only [Finset.sum_mul]
  unfold localizedDoubleFormFactor
  rw [he, integral_finsetSum I hi, Finset.mul_sum]

theorem localizedDoubleFormFactor_iteratedDeriv_sum {ι : Type*} (N : ℕ) (hN : 0 < N) (j : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (I : Finset ι) (w : ι → DoubleAngularVector N → ℝ) (hw : ∀ i ∈ I, Continuous (w i)) :
    iteratedDeriv j (fun t => localizedDoubleFormFactor N r t (fun u => ∑ i ∈ I, w i u)) s =
      ∑ i ∈ I, iteratedDeriv j (fun t => localizedDoubleFormFactor N r t (w i)) s := by
  have he : (fun t => localizedDoubleFormFactor N r t (fun u => ∑ i ∈ I, w i u)) =ᶠ[𝓝 s]
      (fun t => ∑ i ∈ I, localizedDoubleFormFactor N r t (w i)) := by
    filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin hr hr1 hm)] with t ht
    exact localizedDoubleFormFactor_sum N hN hr hr1 ht.2 I w hw
  rw [he.iteratedDeriv_eq j]
  exact iteratedDeriv_fun_sum (fun i hi =>
    (localizedDoubleFormFactor_analyticAt N hN hr hr1 hm (w i) (hw i hi)).contDiffAt)

end
end IsingBulk.First
