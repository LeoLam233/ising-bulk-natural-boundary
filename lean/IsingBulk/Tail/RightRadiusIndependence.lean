import IsingBulk.Tail.RightMixedDoubleContour
import IsingBulk.First.RadiusIndependence

/-! Radius-independent actual source form factors on the right-trace domain. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Filter Set
open scoped Topology

theorem right_mixedDoubleFormFactor_x_radius_eq (N : ℕ) (hN : 0 < N) {r R ry : ℝ}
    (hr : 0 < r) (hR : R < 1) (hrR : r ≤ R) (hy : r ≤ ry ∧ ry ≤ R)
    {s : ℂ} (hm : 1+r⁻¹ < (sourceS s).re) :
    mixedDoubleFormFactor N R ry s = mixedDoubleFormFactor N r ry s := by
  unfold mixedDoubleFormFactor
  congr 1
  apply multiCircleIntegral_congr (hr.trans_le hy.1).le N
  intro y hyc
  have hyb : y ∈ annularProduct N r R := by
    intro i
    rw [hyc i]
    exact hy
  exact multiCircleIntegral_radius_eq N hr hrR _ (right_doubleDensity_x_annular N hN hr hR hm y hyb)

/-- All coordinate contours move through the actual pole-free annular region.
The argument uses genuine Fubini when exchanging the x and y groups. -/
theorem right_doubleFormFactor_radius_eq (N : ℕ) (hN : 0 < N) {r R : ℝ}
    (hr : 0 < r) (hR : R < 1) (hrR : r ≤ R) {s : ℂ}
    (hm : 1+r⁻¹ < (sourceS s).re) : doubleFormFactor N R s = doubleFormFactor N r s := by
  change mixedDoubleFormFactor N R R s = mixedDoubleFormFactor N r r s
  calc
    _ = mixedDoubleFormFactor N r R s :=
      right_mixedDoubleFormFactor_x_radius_eq N hN hr hR hrR ⟨hrR, le_rfl⟩ hm
    _ = mixedDoubleFormFactor N R r s :=
      right_mixedDoubleFormFactor_swap N hN hr hR ⟨le_rfl, hrR⟩ ⟨hrR, le_rfl⟩ hm
    _ = _ := right_mixedDoubleFormFactor_x_radius_eq N hN hr hR hrR ⟨le_rfl, hrR⟩ hm

theorem right_doubleFormFactor_radius_independent (N : ℕ) (hN : 0 < N) {r R : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hR : 0 < R) (hR1 : R < 1) {s : ℂ}
    (hmr : 1+r⁻¹ < (sourceS s).re) (hmR : 1+R⁻¹ < (sourceS s).re) :
    doubleFormFactor N r s = doubleFormFactor N R s := by
  rcases le_total r R with hle | hle
  · exact (right_doubleFormFactor_radius_eq N hN hr hR1 hle hmr).symm
  · exact right_doubleFormFactor_radius_eq N hN hR hr1 hle hmR


def rightCanonicalRadius (s : ℂ) : ℝ := ((sourceS s).re/2)⁻¹

theorem rightCanonicalRadius_admissible {s : ℂ} (hs : 2 < (sourceS s).re) :
    0 < rightCanonicalRadius s ∧ rightCanonicalRadius s < 1 ∧
      1+(rightCanonicalRadius s)⁻¹ < (sourceS s).re := by
  have hp : 1 < (sourceS s).re/2 := by linarith
  refine ⟨inv_pos.mpr (by linarith),inv_lt_one_of_one_lt₀ hp,?_⟩
  simp only [rightCanonicalRadius,inv_inv]
  linarith

def rightFormFactor (N : ℕ) (s : ℂ) : ℂ := doubleFormFactor N (rightCanonicalRadius s) s

theorem rightFormFactor_eq_fixed_radius (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : 1+r⁻¹ < (sourceS s).re) :
    rightFormFactor N s = doubleFormFactor N r s := by
  have hi : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  have hS : 2 < (sourceS s).re := by linarith
  obtain ⟨hc0,hc1,hcm⟩ := rightCanonicalRadius_admissible hS
  exact right_doubleFormFactor_radius_independent N hN hc0 hc1 hr hr1 hcm hm

theorem rightFormFactor_eventually_fixed_radius (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : 1+r⁻¹ < (sourceS s).re) :
    rightFormFactor N =ᶠ[𝓝 s] (fun t => doubleFormFactor N r t) := by
  have hi : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  have hS : 2 < (sourceS s).re := by linarith
  have hs0 : s ≠ 0 := by intro he; norm_num [he,sourceS] at hS
  have hcont : ContinuousAt (fun t : ℂ => (sourceS t).re) s :=
    Complex.continuous_re.continuousAt.comp_of_eq
      (continuousAt_id.add (continuousAt_id.inv₀ hs0)) rfl
  filter_upwards [hcont.eventually (Ioi_mem_nhds hm)] with t ht
  exact rightFormFactor_eq_fixed_radius N hN hr hr1 ht

theorem rightFormFactor_iteratedDeriv_fixed_radius (N : ℕ) (hN : 0 < N) (j : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : 1+r⁻¹ < (sourceS s).re) :
    iteratedDeriv j (rightFormFactor N) s = iteratedDeriv j (doubleFormFactor N r) s :=
  Filter.EventuallyEq.iteratedDeriv_eq j (rightFormFactor_eventually_fixed_radius N hN hr hr1 hm)

theorem rightFormFactor_eq_upper (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : 2 < (sourceS s).re) (hu : 0 < (sourceS s).im) :
    rightFormFactor N s = upperFormFactor N s := by
  obtain ⟨hr,hr1,hmr⟩ := rightCanonicalRadius_admissible hs
  obtain ⟨hu0,hu1,hmu⟩ := canonicalRadius_admissible hu
  let R := max (rightCanonicalRadius s) (canonicalRadius s)
  have hR : 0 < R := hr.trans_le (le_max_left _ _)
  have hR1 : R < 1 := max_lt hr1 hu1
  have hir : R⁻¹ ≤ (rightCanonicalRadius s)⁻¹ := inv_anti₀ hr (le_max_left _ _)
  have hiu : R⁻¹ ≤ (canonicalRadius s)⁻¹ := inv_anti₀ hu0 (le_max_right _ _)
  have hmrR : 1+R⁻¹ < (sourceS s).re := by linarith
  have hmuR : R⁻¹-R < (sourceS s).im := by
    have := le_max_right (rightCanonicalRadius s) (canonicalRadius s)
    change canonicalRadius s ≤ R at this
    linarith
  rw [rightFormFactor_eq_fixed_radius N hN hR hR1 hmrR,
    upperFormFactor_eq_fixed_radius N hN hR hR1 hmuR]

end
end IsingBulk.Tail
