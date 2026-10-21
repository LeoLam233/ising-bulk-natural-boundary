import IsingBulk.First.OnsiteRadiusIndependence

/-! The all-particle onsite source has its own canonical representative.
Its definition does not discard onsite terms or assume convergence. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First Filter Set
open scoped Topology

def upperOnsiteFormFactor (N : ℕ) (s : ℂ) : ℂ :=
  onsiteFormFactor N (canonicalRadius s) s

theorem upperOnsiteFormFactor_eq_fixed_radius (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    upperOnsiteFormFactor N s = onsiteFormFactor N r s := by
  have hi : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  have hS : 0 < (sourceS s).im := by linarith
  obtain ⟨hc0,hc1,hcm⟩ := canonicalRadius_admissible hS
  exact onsiteFormFactor_radius_independent N hN hc0 hc1 hr hr1 hcm hm

theorem upperOnsiteFormFactor_eventually_fixed_radius (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    upperOnsiteFormFactor N =ᶠ[𝓝 s] (fun t => onsiteFormFactor N r t) := by
  filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin hr hr1 hm)] with t ht
  exact upperOnsiteFormFactor_eq_fixed_radius N hN hr hr1 ht.2

theorem upperOnsiteFormFactor_iteratedDeriv_fixed_radius (N : ℕ) (hN : 0 < N)
    (j : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im) :
    iteratedDeriv j (upperOnsiteFormFactor N) s =
      iteratedDeriv j (onsiteFormFactor N r) s :=
  Filter.EventuallyEq.iteratedDeriv_eq j
    (upperOnsiteFormFactor_eventually_fixed_radius N hN hr hr1 hm)

theorem upperOnsiteFormFactor_analyticAt (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : 0 < (sourceS s).im) : AnalyticAt ℂ (upperOnsiteFormFactor N) s := by
  obtain ⟨hr,hr1,hm⟩ := canonicalRadius_admissible hs
  exact ((formFactors_analyticAt N hN hr hr1 hm).2.1).congr
    (upperOnsiteFormFactor_eventually_fixed_radius N hN hr hr1 hm).symm

end
end IsingBulk.HT.Final
