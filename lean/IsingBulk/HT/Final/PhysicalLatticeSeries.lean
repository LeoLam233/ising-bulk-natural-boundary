import IsingBulk.HT.Contour.PhysicalLatticeSummation
import IsingBulk.HT.Final.RightFullSeries

/-! Attachment of the actual all-site lattice coefficients to the complete
odd source series. The inner sum is over the whole square lattice, and the
outer sum ranges over every odd positive particle number.

The pointwise full-lattice identity and its absolute convergence are proved
in `PhysicalLatticeSummation`. Odd-particle convergence is inherited from
the actual right-chart normal-convergence theorem. No statistical-mechanical
representation, angular Fourier identity or natural-boundary assumption is
used here. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open scoped BigOperators

/-- Complete odd sum of the actual two-dimensional lattice coefficients. -/
def physicalFullLatticeOddSeries (t : ℝ) : ℂ :=
  ∑' n : ℕ, ∑' v : ℤ × ℤ, physicalFullLatticeCoefficient (2*n+1) t v

theorem physical_real_trace_gt_two {t : ℝ} (ht : 1 < t) :
    2 < (sourceS (t:ℂ)).re := by
  simpa only [sourceS,Complex.add_re,Complex.ofReal_re,← Complex.ofReal_inv] using
    physical_trace_gt_two ht

/-- There is one common admissible interior-radius threshold for all
particle numbers, with the margin valid at every larger radius below one. -/
theorem physical_real_common_radius {t : ℝ} (ht : 1 < t) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < 1 ∧
      ∀ r : ℝ, r₀ < r → r < 1 → 1+r⁻¹ < (sourceS (t:ℂ)).re := by
  obtain ⟨hr₀,hr₀1,hm₀⟩ := rightCanonicalRadius_admissible
    (physical_real_trace_gt_two ht)
  refine ⟨rightCanonicalRadius (t:ℂ),hr₀,hr₀1,?_⟩
  intro r hr _
  have hi := inv_anti₀ hr₀ hr.le
  linarith

/-- No coordinate or particle cutoff enters the source identification. -/
theorem physicalFullLatticeOddSeries_eq_fixedOddFullSeries {t r : ℝ}
    (ht : 1 < t) (hr : 0 < r) (hr1 : r < 1)
    (hm : 1+r⁻¹ < (sourceS (t:ℂ)).re) :
    physicalFullLatticeOddSeries t = fixedOddFullSeries r (t:ℂ) := by
  apply tsum_congr
  intro n
  exact physicalFullLatticeCoefficient_tsum_eq_standardFormFactor
    (2*n+1) (by omega) ht hr hr1 hm

/-- Absolute convergence of the particle series of full-lattice
coefficients is proved independently of the physical input predicate.
This statement does not interchange the particle and lattice sums. -/
theorem physicalFullLattice_odd_norm_summable {t : ℝ} (ht : 1 < t) :
    Summable (fun n : ℕ =>
      ‖∑' v : ℤ × ℤ, physicalFullLatticeCoefficient (2*n+1) t v‖) := by
  have hS := physical_real_trace_gt_two ht
  obtain ⟨hr,hr1,hm⟩ := rightCanonicalRadius_admissible hS
  have hs : Summable (fun n : ℕ => ‖rightFullCoefficient (2*n+1) (t:ℂ)‖) := by
    simpa only [iteratedDeriv_zero] using rightFullOdd_derivative_summable 0 hS
  apply hs.congr
  intro n
  rw [physicalFullLatticeCoefficient_tsum_eq_standardFormFactor
    (2*n+1) (by omega) ht hr hr1 hm,
    rightFullCoefficient_eq_fixed_radius (2*n+1) (by omega) hr hr1 hm]

/-- The complete physical lattice coefficient series is summable. -/
theorem physicalFullLattice_odd_summable {t : ℝ} (ht : 1 < t) :
    Summable (fun n : ℕ =>
      ∑' v : ℤ × ℤ, physicalFullLatticeCoefficient (2*n+1) t v) :=
  (physicalFullLattice_odd_norm_summable ht).of_norm

end
end IsingBulk.HT.Final
