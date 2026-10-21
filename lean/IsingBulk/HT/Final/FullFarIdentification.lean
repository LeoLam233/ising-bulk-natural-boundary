import IsingBulk.HT.Final.FullSourceConjugation
import IsingBulk.HT.Final.PhysicalGermSeed

/-! The genuine full-site trace representatives agree with the literal
quarter-radius germ near infinity, with no continuation certificate. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators

theorem upperFullCoefficient_eq_quarter_far (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hu : 0 < (sourceS s).im) (hs : 16 < ‖s‖) :
    upperFullCoefficient N s = standardFormFactor N (1/4) s := by
  obtain ⟨hr,hr1,hm⟩ := canonicalRadius_admissible hu
  let R : ℝ := max (1/4) (canonicalRadius s)
  have hR : 0 < R := hr.trans_le (le_max_right _ _)
  have hR1 : R < 1 := max_lt (by norm_num) hr1
  have hmr : R⁻¹-R < (sourceS s).im :=
    (inverse_radius_drop_mono hr (le_max_right _ _)).trans_lt hm
  rw [upperFullCoefficient_eq_fixed_radius N hN hR hR1 hmr]
  exact standardFormFactor_far_radius_eq N hN (le_max_left _ _) hR1 hs

theorem rightFullCoefficient_eq_quarter_far (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hu : 2 < (sourceS s).re) (hs : 16 < ‖s‖) :
    rightFullCoefficient N s = standardFormFactor N (1/4) s := by
  obtain ⟨hr,hr1,hm⟩ := rightCanonicalRadius_admissible hu
  let R : ℝ := max (1/4) (rightCanonicalRadius s)
  have hR : 0 < R := hr.trans_le (le_max_right _ _)
  have hR1 : R < 1 := max_lt (by norm_num) hr1
  have hi : R⁻¹ ≤ (rightCanonicalRadius s)⁻¹ := inv_anti₀ hr (le_max_right _ _)
  have hmr : 1+R⁻¹ < (sourceS s).re := by linarith
  rw [rightFullCoefficient_eq_fixed_radius N hN hR hR1 hmr]
  exact standardFormFactor_far_radius_eq N hN (le_max_left _ _) hR1 hs

theorem leftFullCoefficient_eq_quarter_far (N : ℕ) (hN : 0 < N) {s : ℂ}
    (hu : (sourceS s).re < -2) (hs : 16 < ‖s‖) :
    leftFullCoefficient N s = standardFormFactor N (1/4) s := by
  obtain ⟨hr,hr1,hm⟩ := leftCanonicalRadius_admissible hu
  let R : ℝ := max (1/4) (leftCanonicalRadius s)
  have hR : 0 < R := hr.trans_le (le_max_right _ _)
  have hR1 : R < 1 := max_lt (by norm_num) hr1
  have hi : R⁻¹ ≤ (leftCanonicalRadius s)⁻¹ := inv_anti₀ hr (le_max_right _ _)
  have hmr : 1+R⁻¹ < -(sourceS s).re := by linarith
  rw [leftFullCoefficient_eq_fixed_radius N hN hR hR1 hmr]
  exact standardFormFactor_far_radius_eq N hN (le_max_left _ _) hR1 hs

theorem upperFullOddSeries_eq_quarter_far {s : ℂ}
    (hu : 0 < (sourceS s).im) (hs : 16 < ‖s‖) :
    upperFullOddSeries s = fixedOddFullSeries (1/4) s := by
  apply tsum_congr
  intro n
  exact upperFullCoefficient_eq_quarter_far _ (by omega) hu hs

theorem rightFullOddSeries_eq_quarter_far {s : ℂ}
    (hu : 2 < (sourceS s).re) (hs : 16 < ‖s‖) :
    rightFullOddSeries s = fixedOddFullSeries (1/4) s := by
  apply tsum_congr
  intro n
  exact rightFullCoefficient_eq_quarter_far _ (by omega) hu hs

/-- Physical input attaches to the actual constructed right-chart full sum
on the physical real germ. The sum includes its one-particle onsite term. -/
theorem physical_right_real_germ {X : ℂ → ℂ} (hrep : RealFullBulkRepresentation X)
    {x : ℝ} (hx : 0 < x) (hxsmall : x < 1/16) :
    X (x:ℂ) = exteriorPrefactor ((x:ℂ)⁻¹)*rightFullOddSeries ((x:ℂ)⁻¹) := by
  have hfar : 16 < ‖((x:ℂ)⁻¹)‖ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx,inv_eq_one_div]
    apply (lt_div_iff₀ hx).mpr
    linarith
  have hxi : 1 < x⁻¹ := by
    apply (one_lt_inv₀ hx).mpr
    linarith
  have hr : 2 < (sourceS ((x:ℂ)⁻¹)).re := by
    simpa [sourceS,← Complex.ofReal_inv] using real_trace_gt_two hxi
  rw [rightFullOddSeries_eq_quarter_far hr hfar]
  exact normalized_real_germ_identification hrep hx hxsmall

end
end IsingBulk.HT.Final
