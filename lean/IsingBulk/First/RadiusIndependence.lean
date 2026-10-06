import IsingBulk.First.MixedDoubleContour
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Radius independence and fixed-radius derivative locality for the actual
source form factor on the selected upper-trace exterior domain. -/
namespace IsingBulk.First
noncomputable section
open Filter Set
open scoped Topology

theorem mixedDoubleFormFactor_x_radius_eq (N : ℕ) (hN : 0 < N) {r R ry : ℝ}
    (hr : 0 < r) (hR : R < 1) (hrR : r ≤ R) (hy : r ≤ ry ∧ ry ≤ R)
    {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    mixedDoubleFormFactor N R ry s = mixedDoubleFormFactor N r ry s := by
  unfold mixedDoubleFormFactor
  congr 1
  apply multiCircleIntegral_congr (hr.trans_le hy.1).le N
  intro y hyc
  have hyb : y ∈ annularProduct N r R := by
    intro i
    rw [hyc i]
    exact hy
  exact multiCircleIntegral_radius_eq N hr hrR _ (doubleDensity_x_annular N hN hr hR hm y hyb)

/-- All coordinate contours move through the actual pole-free annular region.
The argument uses genuine Fubini when exchanging the x and y groups. -/
theorem doubleFormFactor_radius_eq (N : ℕ) (hN : 0 < N) {r R : ℝ}
    (hr : 0 < r) (hR : R < 1) (hrR : r ≤ R) {s : ℂ}
    (hm : r⁻¹-r < (sourceS s).im) : doubleFormFactor N R s = doubleFormFactor N r s := by
  change mixedDoubleFormFactor N R R s = mixedDoubleFormFactor N r r s
  calc
    _ = mixedDoubleFormFactor N r R s :=
      mixedDoubleFormFactor_x_radius_eq N hN hr hR hrR ⟨hrR, le_rfl⟩ hm
    _ = mixedDoubleFormFactor N R r s :=
      mixedDoubleFormFactor_swap N hN hr hR ⟨le_rfl, hrR⟩ ⟨hrR, le_rfl⟩ hm
    _ = _ := mixedDoubleFormFactor_x_radius_eq N hN hr hR hrR ⟨le_rfl, hrR⟩ hm

theorem doubleFormFactor_radius_independent (N : ℕ) (hN : 0 < N) {r R : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hR : 0 < R) (hR1 : R < 1) {s : ℂ}
    (hmr : r⁻¹-r < (sourceS s).im) (hmR : R⁻¹-R < (sourceS s).im) :
    doubleFormFactor N r s = doubleFormFactor N R s := by
  rcases le_total r R with hle | hle
  · exact (doubleFormFactor_radius_eq N hN hr hR1 hle hmr).symm
  · exact doubleFormFactor_radius_eq N hN hR hr1 hle hmR

/-- A concrete admissible reference radius on Im(S)>0; this is not a physical
change to the integrand. Its independence is proved before taking derivatives. -/
def canonicalRadius (s : ℂ) : ℝ := (1+(sourceS s).im/4)⁻¹

theorem canonicalRadius_admissible {s : ℂ} (hs : 0 < (sourceS s).im) :
    0 < canonicalRadius s ∧ canonicalRadius s < 1 ∧
      (canonicalRadius s)⁻¹-canonicalRadius s < (sourceS s).im := by
  have hp : 0 < 1+(sourceS s).im/4 := by linarith
  have hl : 1 < 1+(sourceS s).im/4 := by linarith
  have hi : 1-(sourceS s).im/4 ≤ (1+(sourceS s).im/4)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hp).mpr
    nlinarith [sq_nonneg ((sourceS s).im)]
  refine ⟨inv_pos.mpr hp, inv_lt_one_of_one_lt₀ hl, ?_⟩
  simp only [canonicalRadius, inv_inv]
  linarith

/-- A radius-independent representative of the actual normalized source object
on the open upper-trace domain. -/
def upperFormFactor (N : ℕ) (s : ℂ) : ℂ := doubleFormFactor N (canonicalRadius s) s

theorem upperFormFactor_eq_fixed_radius (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    upperFormFactor N s = doubleFormFactor N r s := by
  have hi : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  have hS : 0 < (sourceS s).im := by linarith
  obtain ⟨hc0, hc1, hcm⟩ := canonicalRadius_admissible hS
  exact doubleFormFactor_radius_independent N hN hc0 hc1 hr hr1 hcm hm

/-- Local equality holds on a genuine complex parameter neighborhood before any
s differentiation. The radius on the right is a fixed real number. -/
theorem upperFormFactor_eventually_fixed_radius (N : ℕ) (hN : 0 < N) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    upperFormFactor N =ᶠ[𝓝 s] (fun t => doubleFormFactor N r t) := by
  have hi : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  have hS : 0 < (sourceS s).im := by linarith
  have hs0 : s ≠ 0 := by intro he; simp [he, sourceS] at hS
  have hcont : ContinuousAt (fun t : ℂ => (sourceS t).im) s := by
    exact Complex.continuous_im.continuousAt.comp_of_eq
      (continuousAt_id.add (continuousAt_id.inv₀ hs0)) rfl
  filter_upwards [hcont.eventually (Ioi_mem_nhds hm)] with t ht
  exact upperFormFactor_eq_fixed_radius N hN hr hr1 ht

/-- Every actual complex derivative order uses the same fixed-radius source
function locally; no derivative of the radius function occurs. -/
theorem upperFormFactor_iteratedDeriv_fixed_radius (N : ℕ) (hN : 0 < N) (j : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {s : ℂ} (hm : r⁻¹-r < (sourceS s).im) :
    iteratedDeriv j (upperFormFactor N) s = iteratedDeriv j (fun t => doubleFormFactor N r t) s :=
  Filter.EventuallyEq.iteratedDeriv_eq j (upperFormFactor_eventually_fixed_radius N hN hr hr1 hm)

end
end IsingBulk.First
