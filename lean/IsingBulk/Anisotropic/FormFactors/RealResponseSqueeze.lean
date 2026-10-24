import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-! The analytic squeeze used in ANISO §1.1 for the real uniform-field
response. Gibbs/GHS hypotheses are not asserted here. Once their explicit
finite-local-field consequences and covariance summability are established,
this theorem proves the right derivative without exchanging an uncontrolled
field limit and a lattice sum. -/
namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open Set Filter
open scoped Topology

/-- Local fields give arbitrarily accurate derivative lower bounds; finite
volume concavity gives the common upper secant bound. Their combination
proves the actual right derivative, not a definition named "response". -/
theorem uniform_field_right_derivative (m : ℝ → ℝ) (localField : ℕ → ℝ → ℝ)
    (d : ℕ → ℝ) (L : ℝ)
    (hzero : ∀ n, localField n 0 = m 0)
    (hlower : ∀ n h, 0 < h → localField n h ≤ m h)
    (hlocal : ∀ n, HasDerivAt (localField n) (d n) 0)
    (hd : Tendsto d atTop (𝓝 L))
    (hupper : ∀ h, 0 < h → m h-m 0 ≤ L*h) :
    HasDerivWithinAt m L (Ioi 0) 0 := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Ioi 0)).mpr
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨n,hn⟩ := (hd.eventually (Ioi_mem_nhds ha)).exists
    have hlocalLimit : Tendsto (slope (localField n) 0) (𝓝[Ioi (0:ℝ)] 0) (𝓝 (d n)) :=
      (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0:ℝ) ∉ Ioi 0)).mp
        (hlocal n).hasDerivWithinAt
    filter_upwards [hlocalLimit.eventually (Ioi_mem_nhds hn),self_mem_nhdsWithin] with h hgt hh
    apply hgt.trans_le
    simp only [slope_def_field,sub_zero,hzero]
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hlower n h hh) _) (le_of_lt hh)
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with h hh
    apply lt_of_le_of_lt _ ha
    simp only [slope_def_field,sub_zero]
    exact (div_le_iff₀ hh).mpr (hupper h hh)
end
end IsingBulk.Anisotropic.FormFactors
