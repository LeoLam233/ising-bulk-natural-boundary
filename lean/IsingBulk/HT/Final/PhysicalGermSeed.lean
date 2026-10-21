import IsingBulk.HT.Final.NearInfinityFullSeries

/-! Physical identification of the actual internally defined full odd contour
series near s=0, conditional only on the explicit real HT representation.
No lattice-state identity is inferred from LT E1/E2. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Final Set

/-- Every permitted sufficiently large radius gives the same actual full
odd sum as the fixed quarter-radius seed, throughout its far exterior. -/
theorem fixedOddFullSeries_far_radius_eq {r : ℝ}
    (hr : (1/4:ℝ) ≤ r) (hr1 : r < 1) {t : ℂ} (ht : 16 < ‖t‖) :
    fixedOddFullSeries r t = fixedOddFullSeries (1/4) t := by
  apply tsum_congr
  intro n
  exact standardFormFactor_far_radius_eq (2*n+1) (by omega) hr hr1 ht

/-- This real germ is the full bulk observable specified by the input
representation, not the LT even-particle series. -/
theorem normalized_real_germ_identification {X : ℂ → ℂ}
    (hrep : RealFullBulkRepresentation X) {x : ℝ}
    (hx : 0 < x) (hxsmall : x < 1/16) :
    X (x:ℂ) = fixedNormalizedBulk (1/4) ((x:ℂ)⁻¹) := by
  have hx1 : x < 1 := by linarith
  obtain ⟨r₀,hr₀,hr₀1,h⟩ := hrep x hx hx1
  let r : ℝ := (max r₀ (1/4)+1)/2
  have hm : max r₀ (1/4) < 1 := max_lt hr₀1 (by norm_num)
  have hr0 : r₀ < r := by dsimp [r]; linarith [le_max_left r₀ (1/4)]
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hrq : (1/4:ℝ) ≤ r := by dsimp [r]; linarith [le_max_right r₀ (1/4)]
  have hfar : 16 < ‖((x:ℂ)⁻¹)‖ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx,inv_eq_one_div]
    apply (lt_div_iff₀ hx).mpr
    linarith
  have he := (h r hr0 hr1).2
  rw [fixedOddFullSeries_far_radius_eq hrq hr1 hfar] at he
  have hp : interiorPrefactor (x:ℂ)=exteriorPrefactor ((x:ℂ)⁻¹) := by
    simpa only [inv_inv] using interiorPrefactor_inv ((x:ℂ)⁻¹)
  simpa only [fixedNormalizedBulk,hp] using he

/-- Actual susceptibility identification in the prescribed physical interval.
The statistical-mechanical representation remains an explicit premise. -/
theorem susceptibility_real_germ_identification {J : ℝ} (hJ : 0 < J)
    {chi : ℂ → ℂ} (hrep : PhysicalSusceptibilityRepresentation J chi)
    {x : ℝ} (hx : 0 < x) (hxsmall : x < 1/16) :
    chi (x:ℂ) = inverseTemperatureBranch J (x:ℂ)*
      fixedNormalizedBulk (1/4) ((x:ℂ)⁻¹) := by
  have he := normalized_real_germ_identification hrep hx hxsmall
  have hb0 := (inverseTemperatureBranch_regular
    (show 0 < (x:ℂ).re by simpa using hx) hJ).2
  have he' := (div_eq_iff hb0).mp he
  simpa only [mul_comm] using he'

end
end IsingBulk.HT.Final
