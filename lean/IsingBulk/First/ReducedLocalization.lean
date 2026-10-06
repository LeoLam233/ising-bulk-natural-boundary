import IsingBulk.First.RadiusIndependence
import IsingBulk.First.GlobalResidueRoot
import IsingBulk.First.LocalizedPartition

/-! The actual two selected reduced pieces and untouched angular complement
agree with the source form factor on an open parameter neighborhood. -/
namespace IsingBulk.First
noncomputable section
open Filter Set
open scoped Topology

def reducedLocalizedSum (N : ℕ) (r : ℝ) (u v : (Fin N → ℝ) → ℝ) (s : ℂ) : ℂ :=
  weightedReducedFormFactor N r (globalRoot s) u + weightedReducedFormFactor N r (globalRoot s) v +
    localizedDoubleFormFactor N r s (fun p => 1-u p.2-v p.2)

theorem upperFormFactor_reduced_localization (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (u v : (Fin N → ℝ) → ℝ) (hu : Continuous u) (hv : Continuous v) :
    upperFormFactor N s = reducedLocalizedSum N r u v s := by
  have ha := globalRoot_admissible hr hr1 hm
  have ht : ∀ θ : Fin N → ℝ, ResidueAdmissible r s (angleTuple r θ)
      (fun i => globalRoot s (anglePoint r (θ i))) := by
    intro θ
    apply ha.toTuple N (angleTuple r θ)
    intro i
    exact anglePoint_norm hr.le _
  rw [upperFormFactor_eq_fixed_radius N hN hr hr1 hm]
  have hh := compatible_localization_identity N hN r s (globalRoot s) ht u v hu hv
  rw [weighted_residue_reduction N hN r s (globalRoot s) u ht,
    weighted_residue_reduction N hN r s (globalRoot s) v ht] at hh
  exact hh

theorem upperFormFactor_eventually_reduced_localization (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (u v : (Fin N → ℝ) → ℝ) (hu : Continuous u) (hv : Continuous v) :
    upperFormFactor N =ᶠ[𝓝 s] reducedLocalizedSum N r u v := by
  have hi : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  have hS : 0 < (sourceS s).im := by linarith
  have hs0 : s ≠ 0 := by intro he; simp [he, sourceS] at hS
  have hcont : ContinuousAt (fun t : ℂ => (sourceS t).im) s := by
    exact Complex.continuous_im.continuousAt.comp_of_eq
      (continuousAt_id.add (continuousAt_id.inv₀ hs0)) rfl
  filter_upwards [hcont.eventually (Ioi_mem_nhds hm)] with t ht
  exact upperFormFactor_reduced_localization N hN hr hr1 ht u v hu hv

/-- Local equality is established before taking any order of actual complex derivative. -/
theorem upperFormFactor_iteratedDeriv_reduced_localization (N : ℕ) (hN : 0 < N) (j : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im)
    (u v : (Fin N → ℝ) → ℝ) (hu : Continuous u) (hv : Continuous v) :
    iteratedDeriv j (upperFormFactor N) s = iteratedDeriv j (reducedLocalizedSum N r u v) s :=
  Filter.EventuallyEq.iteratedDeriv_eq j
    (upperFormFactor_eventually_reduced_localization N hN hr hr1 hm u v hu hv)

end
end IsingBulk.First
