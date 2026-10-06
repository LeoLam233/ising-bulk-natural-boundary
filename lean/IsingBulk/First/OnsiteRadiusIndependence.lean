import IsingBulk.First.MixedOnsiteContour
import IsingBulk.First.FormFactorAnalytic

/-! Onsite radius independence through the genuine pole-free annular region.
The local-neighborhood equality is established before any temperature derivative. -/
namespace IsingBulk.First
noncomputable section
open Filter Set
open scoped Topology

theorem mixedOnsiteFormFactor_x_radius_eq (N : ℕ) (hN : 0 < N) {r R ry : ℝ}
    (hr : 0 < r) (hR : R < 1) (hrR : r ≤ R) (hy : r ≤ ry ∧ ry ≤ R)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    mixedOnsiteFormFactor N R ry s = mixedOnsiteFormFactor N r ry s := by
  unfold mixedOnsiteFormFactor
  congr 1
  apply multiCircleIntegral_congr (hr.trans_le hy.1).le N
  intro y hyc
  have hyb : y ∈ annularProduct N r R := by
    intro i
    rw [hyc i]
    exact hy
  exact multiCircleIntegral_radius_eq N hr hrR _ (onsiteDensity_x_annular N hN hr hR hm y hyb)

/-- All coordinate contours move through the actual pole-free annular region.
The argument uses genuine Fubini when exchanging the x and y groups. -/
theorem onsiteFormFactor_radius_eq (N : ℕ) (hN : 0 < N) {r R : ℝ}
    (hr : 0 < r) (hR : R < 1) (hrR : r ≤ R) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im) : onsiteFormFactor N R s = onsiteFormFactor N r s := by
  change mixedOnsiteFormFactor N R R s = mixedOnsiteFormFactor N r r s
  calc
    _ = mixedOnsiteFormFactor N r R s :=
      mixedOnsiteFormFactor_x_radius_eq N hN hr hR hrR ⟨hrR, le_rfl⟩ hm
    _ = mixedOnsiteFormFactor N R r s :=
      mixedOnsiteFormFactor_swap N hN hr hR ⟨le_rfl, hrR⟩ ⟨hrR, le_rfl⟩ hm
    _ = _ := mixedOnsiteFormFactor_x_radius_eq N hN hr hR hrR ⟨le_rfl, hrR⟩ hm

theorem onsiteFormFactor_radius_independent (N : ℕ) (hN : 0 < N) {r R : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hR : 0 < R) (hR1 : R < 1) {s : ℂ}
    (hmr : r⁻¹-r < (sourceS s).im) (hmR : R⁻¹-R < (sourceS s).im) :
    onsiteFormFactor N r s = onsiteFormFactor N R s := by
  rcases le_total r R with hle | hle
  · exact (onsiteFormFactor_radius_eq N hN hr hR1 hle hmr).symm
  · exact onsiteFormFactor_radius_eq N hN hR hr1 hle hmR

theorem onsiteFormFactor_eventually_radius_eq (N : ℕ) (hN : 0 < N) {r R : ℝ}
    (hr : 0 < r) (hR : R < 1) (hrR : r ≤ R) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im) :
    (fun t => onsiteFormFactor N R t) =ᶠ[𝓝 s] (fun t => onsiteFormFactor N r t) := by
  filter_upwards [dampingDomain_mem_nhds (dampingDomain_of_margin hr (hrR.trans_lt hR) hm)] with t ht
  exact onsiteFormFactor_radius_eq N hN hr hR hrR ht.2

/-- The larger permitted TW radius and the fixed source radius have the same
actual complex derivative of every order. R itself is never differentiated. -/
theorem onsiteFormFactor_iteratedDeriv_radius_eq (N : ℕ) (hN : 0 < N) (j : ℕ) {r R : ℝ}
    (hr : 0 < r) (hR : R < 1) (hrR : r ≤ R) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im) :
    iteratedDeriv j (onsiteFormFactor N R) s = iteratedDeriv j (onsiteFormFactor N r) s :=
  Filter.EventuallyEq.iteratedDeriv_eq j (onsiteFormFactor_eventually_radius_eq N hN hr hR hrR hm)

end
end IsingBulk.First
