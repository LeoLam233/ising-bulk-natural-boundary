import IsingBulk.HT.Final.LeftOffsiteMixedContour
import IsingBulk.First.RadiusIndependence

/-! Radius-independent actual source form factors on the left-trace domain. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail Filter Set
open scoped Topology

theorem left_mixedDoubleFormFactor_x_radius_eq (N : ℕ) (hN : 0 < N) {r R ry : ℝ}
    (hr : 0 < r) (hR : R < 1) (hrR : r ≤ R) (hy : r ≤ ry ∧ ry ≤ R)
    {s : ℂ} (hm : 1+r⁻¹ < -(sourceS s).re) :
    mixedDoubleFormFactor N R ry s = mixedDoubleFormFactor N r ry s := by
  unfold mixedDoubleFormFactor
  congr 1
  apply multiCircleIntegral_congr (hr.trans_le hy.1).le N
  intro y hyc
  have hyb : y ∈ annularProduct N r R := by
    intro i
    rw [hyc i]
    exact hy
  exact multiCircleIntegral_radius_eq N hr hrR _ (left_doubleDensity_x_annular N hN hr hR hm y hyb)

/-- All coordinate contours move through the actual pole-free annular region.
The argument uses genuine Fubini when exchanging the x and y groups. -/
theorem left_doubleFormFactor_radius_eq (N : ℕ) (hN : 0 < N) {r R : ℝ}
    (hr : 0 < r) (hR : R < 1) (hrR : r ≤ R) {s : ℂ}
    (hm : 1+r⁻¹ < -(sourceS s).re) : doubleFormFactor N R s = doubleFormFactor N r s := by
  change mixedDoubleFormFactor N R R s = mixedDoubleFormFactor N r r s
  calc
    _ = mixedDoubleFormFactor N r R s :=
      left_mixedDoubleFormFactor_x_radius_eq N hN hr hR hrR ⟨hrR, le_rfl⟩ hm
    _ = mixedDoubleFormFactor N R r s :=
      left_mixedDoubleFormFactor_swap N hN hr hR ⟨le_rfl, hrR⟩ ⟨hrR, le_rfl⟩ hm
    _ = _ := left_mixedDoubleFormFactor_x_radius_eq N hN hr hR hrR ⟨le_rfl, hrR⟩ hm

theorem left_doubleFormFactor_radius_independent (N : ℕ) (hN : 0 < N) {r R : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hR : 0 < R) (hR1 : R < 1) {s : ℂ}
    (hmr : 1+r⁻¹ < -(sourceS s).re) (hmR : 1+R⁻¹ < -(sourceS s).re) :
    doubleFormFactor N r s = doubleFormFactor N R s := by
  rcases le_total r R with hle | hle
  · exact (left_doubleFormFactor_radius_eq N hN hr hR1 hle hmr).symm
  · exact left_doubleFormFactor_radius_eq N hN hR hr1 hle hmR


def leftCanonicalRadius (s : ℂ) : ℝ := (-(sourceS s).re/2)⁻¹

theorem leftCanonicalRadius_admissible {s : ℂ} (hs : (sourceS s).re < -2) :
    0 < leftCanonicalRadius s ∧ leftCanonicalRadius s < 1 ∧
      1+(leftCanonicalRadius s)⁻¹ < -(sourceS s).re := by
  have hp : 1 < -(sourceS s).re/2 := by linarith
  refine ⟨inv_pos.mpr (by linarith),inv_lt_one_of_one_lt₀ hp,?_⟩
  simp only [leftCanonicalRadius,inv_inv]
  linarith

def leftFormFactor (N : ℕ) (s : ℂ) : ℂ := doubleFormFactor N (leftCanonicalRadius s) s

theorem leftFormFactor_eq_fixed_radius (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : 1+r⁻¹ < -(sourceS s).re) :
    leftFormFactor N s = doubleFormFactor N r s := by
  have hi : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  have hS : (sourceS s).re < -2 := by linarith
  obtain ⟨hc0,hc1,hcm⟩ := leftCanonicalRadius_admissible hS
  exact left_doubleFormFactor_radius_independent N hN hc0 hc1 hr hr1 hcm hm

theorem leftFormFactor_eventually_fixed_radius (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : 1+r⁻¹ < -(sourceS s).re) :
    leftFormFactor N =ᶠ[𝓝 s] (fun t => doubleFormFactor N r t) := by
  have hi : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  have hS : (sourceS s).re < -2 := by linarith
  have hs0 : s ≠ 0 := by intro he; norm_num [he,sourceS] at hS
  have hcont : ContinuousAt (fun t : ℂ => -(sourceS t).re) s :=
    (Complex.continuous_re.continuousAt.comp_of_eq
      (continuousAt_id.add (continuousAt_id.inv₀ hs0)) rfl).neg
  filter_upwards [hcont.eventually (Ioi_mem_nhds hm)] with t ht
  exact leftFormFactor_eq_fixed_radius N hN hr hr1 ht

theorem leftFormFactor_iteratedDeriv_fixed_radius (N : ℕ) (hN : 0 < N) (j : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : 1+r⁻¹ < -(sourceS s).re) :
    iteratedDeriv j (leftFormFactor N) s = iteratedDeriv j (doubleFormFactor N r) s :=
  Filter.EventuallyEq.iteratedDeriv_eq j (leftFormFactor_eventually_fixed_radius N hN hr hr1 hm)

theorem leftFormFactor_eq_upper (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hs : (sourceS s).re < -2) (hu : 0 < (sourceS s).im) :
    leftFormFactor N s = upperFormFactor N s := by
  obtain ⟨hr,hr1,hmr⟩ := leftCanonicalRadius_admissible hs
  obtain ⟨hu0,hu1,hmu⟩ := canonicalRadius_admissible hu
  let R := max (leftCanonicalRadius s) (canonicalRadius s)
  have hR : 0 < R := hr.trans_le (le_max_left _ _)
  have hR1 : R < 1 := max_lt hr1 hu1
  have hir : R⁻¹ ≤ (leftCanonicalRadius s)⁻¹ := inv_anti₀ hr (le_max_left _ _)
  have hiu : R⁻¹ ≤ (canonicalRadius s)⁻¹ := inv_anti₀ hu0 (le_max_right _ _)
  have hmrR : 1+R⁻¹ < -(sourceS s).re := by linarith
  have hmuR : R⁻¹-R < (sourceS s).im := by
    have := le_max_right (leftCanonicalRadius s) (canonicalRadius s)
    change canonicalRadius s ≤ R at this
    linarith
  rw [leftFormFactor_eq_fixed_radius N hN hR hR1 hmrR,
    upperFormFactor_eq_fixed_radius N hN hR hR1 hmuR]

end
end IsingBulk.HT.Final
