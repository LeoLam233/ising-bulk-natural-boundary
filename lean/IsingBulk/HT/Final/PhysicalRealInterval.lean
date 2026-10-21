import IsingBulk.HT.Final.PhysicalSusceptibilityGerm

/-! Real-interval identification without restricting to the far-temperature
quarter-radius germ. A common admissible radius is chosen from the actual
right chart and the explicit real representation. This removes the artificial
`x < 1/16` restriction from physical identification, not from any analytic
estimate. The representation premise remains explicit. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Final

theorem exteriorOddSeries_eq_right {t : ℂ} (ht : 2 < (sourceS t).re) :
    exteriorOddSeries t = rightFullOddSeries t :=
  tsum_congr (fun n => exteriorOddTerm_eq_right n ht)

/-- The contour-normalized physical identity identifies the constructed
beta-free germ on the entire physical HT interval, not only near zero. -/
theorem physicalBulk_real_interval {X : ℂ → ℂ}
    (hrep : RealFullBulkRepresentation X) {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1) :
    X (x:ℂ) = interiorFullBulk (x:ℂ) := by
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hxi : 1 < x⁻¹ := (one_lt_inv₀ hx).mpr hx1
  have hS : 2 < (sourceS ((x:ℂ)⁻¹)).re := by
    simpa [sourceS,← Complex.ofReal_inv] using real_trace_gt_two hxi
  obtain ⟨hc0,hc1,hcm⟩ := rightCanonicalRadius_admissible hS
  obtain ⟨r₀,_hr₀,hr₀1,hrepR⟩ := hrep x hx hx1
  let R : ℝ := max ((r₀+1)/2) (rightCanonicalRadius ((x:ℂ)⁻¹))
  have hR0 : 0 < R := hc0.trans_le (le_max_right _ _)
  have hR1 : R < 1 := max_lt (by linarith) hc1
  have hr₀R : r₀ < R :=
    lt_of_lt_of_le (by linarith : r₀ < (r₀+1)/2) (le_max_left _ _)
  have hi : R⁻¹ ≤ (rightCanonicalRadius ((x:ℂ)⁻¹))⁻¹ :=
    inv_anti₀ hc0 (le_max_right _ _)
  have hm : 1+R⁻¹ < (sourceS ((x:ℂ)⁻¹)).re := by linarith
  have he := (hrepR R hr₀R hR1).2
  have hP : interiorPrefactor (x:ℂ) = exteriorPrefactor ((x:ℂ)⁻¹) := by
    simpa only [inv_inv] using interiorPrefactor_inv ((x:ℂ)⁻¹)
  rw [interiorFullBulk_eq_exterior hx0,exteriorFullBulk,
    exteriorOddSeries_eq_right hS,rightFullOddSeries_eq_fixed_radius hR0 hR1 hm]
  simpa only [hP] using he

/-- Physical beta is included throughout the whole real HT interval. -/
theorem physicalSusceptibility_real_interval {J : ℝ} (hJ : 0 < J)
    {chi : ℂ → ℂ} (hrep : PhysicalSusceptibilityRepresentation J chi)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    chi (x:ℂ) = interiorPhysicalSusceptibility J (x:ℂ) := by
  have he := physicalBulk_real_interval hrep hx hx1
  have hb := (inverseTemperatureBranch_regular
    (show 0 < (x:ℂ).re by simpa only [Complex.ofReal_re] using hx) hJ).2
  have hid := (div_eq_iff hb).mp he
  simpa only [interiorPhysicalSusceptibility,mul_comm] using hid

end
end IsingBulk.HT.Final
