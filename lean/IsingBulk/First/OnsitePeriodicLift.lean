import IsingBulk.First.DoublePeriodicLiftIntegral
import IsingBulk.First.OnsiteLocalBound

/-! Exact torus/full-space lift and weight-one normalization for the literal
onsite form factor. No offsite smoothness input is used. -/
namespace IsingBulk.First
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

theorem onsiteAngularDensity_periodic (N : ℕ) (r : ℝ) (s : ℂ) :
    DoubleCoordinatePeriodicSections N (doubleAngularDensityOf r (onsiteDensity s)) := by
  constructor
  · intro y x i
    simp only [doubleAngularDensityOf,angleProductJacobian_update_period,angleTuple_update_period]
  · intro x y i
    simp only [doubleAngularDensityOf,angleProductJacobian_update_period,angleTuple_update_period]

theorem onsiteFormFactor_eq_localizedOnsite_one (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    onsiteFormFactor N r s = localizedOnsiteFormFactor N r s (fun _ => 1) := by
  have hO := (normalizationDensities_continuous_angles N hN r s (globalRoot s)
    (globalRoot_admissible hr hr1 hm)).1
  unfold onsiteFormFactor localizedOnsiteFormFactor
  rw [doubleCircleIntegral_eq_product N r _ hO]
  congr 1
  apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
  intro p _
  simp only [localizedOnsiteAngleDensity,Complex.ofReal_one,one_mul]

theorem localizedOnsiteFormFactor_periodicLift (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (c : DoubleAngularVector N) (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (hsmall : ∀ u, w u ≠ 0 → ∀ i, |u.1 i-c.1 i| ≤ 1/2 ∧ |u.2 i-c.2 i| ≤ 1/2) :
    localizedOnsiteFormFactor N r s (doublePeriodicizeBump c w) =
      liftedLocalizedOnsiteFormFactor N r s w := by
  have hO := (normalizationDensities_continuous_angles N hN r s (globalRoot s)
    (globalRoot_admissible hr hr1 hm)).1
  have he := doublePeriodicizeBump_integral N c w hw hsmall
    (doubleAngularDensityOf r (onsiteDensity s))
    (doubleAngularDensityOf_continuous N r _ hO) (onsiteAngularDensity_periodic N r s)
  unfold localizedOnsiteFormFactor liftedLocalizedOnsiteFormFactor
  congr 1
  simpa only [localizedOnsiteAngleDensity,doubleAngularDensityOf,mul_assoc] using he

theorem localizedOnsiteFormFactor_iteratedDeriv_periodicLift (N : ℕ) (hN : 0 < N) (j : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (c : DoubleAngularVector N) (w : DoubleAngularVector N → ℝ) (hw : ContDiff ℝ ∞ w)
    (hsmall : ∀ u, w u ≠ 0 → ∀ i, |u.1 i-c.1 i| ≤ 1/2 ∧ |u.2 i-c.2 i| ≤ 1/2) :
    iteratedDeriv j (fun t => localizedOnsiteFormFactor N r t (doublePeriodicizeBump c w)) s =
      iteratedDeriv j (fun t => liftedLocalizedOnsiteFormFactor N r t w) s := by
  apply Filter.EventuallyEq.iteratedDeriv_eq j
  filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin hr hr1 hm)] with t ht
  exact localizedOnsiteFormFactor_periodicLift N hN hr hr1 ht.2 c w hw hsmall

theorem onsiteFormFactor_iteratedDeriv_eq_localizedOnsite_one (N : ℕ) (hN : 0 < N) (j : ℕ)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    iteratedDeriv j (onsiteFormFactor N r) s =
      iteratedDeriv j (fun t => localizedOnsiteFormFactor N r t (fun _ => 1)) s := by
  apply Filter.EventuallyEq.iteratedDeriv_eq j
  filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin hr hr1 hm)] with t ht
  exact onsiteFormFactor_eq_localizedOnsite_one N hN hr hr1 ht.2

end
end IsingBulk.First
