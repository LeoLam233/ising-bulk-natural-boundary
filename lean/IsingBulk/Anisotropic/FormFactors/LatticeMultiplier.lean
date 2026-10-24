import IsingBulk.Anisotropic.FormFactors.ContourAlgebra
import IsingBulk.HT.Contour.PhysicalLatticeSummation

/-! Genuine ℤ² summability and onsite/axis bookkeeping of the contour
multiplier. All summability is proved before the displayed tsum identity. -/
namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First IsingBulk.HT.Contour
open scoped BigOperators

def latticeMultiplier (X Y : ℂ) (v : ℤ × ℤ) : ℂ :=
  (X^v.1.natAbs*Y^v.2.natAbs)/(X*Y)

theorem latticeMultiplier_norm_summable {X Y : ℂ} (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) :
    Summable (fun v : ℤ × ℤ => ‖latticeMultiplier X Y v‖) := by
  have hSX := physical_twoSided_geometric_norm_summable hX
  have hSY := physical_twoSided_geometric_norm_summable hY
  have hprod := hSX.mul_of_nonneg hSY (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  simpa only [latticeMultiplier,norm_div,norm_mul] using hprod.div_const ‖X*Y‖

theorem latticeMultiplier_summable {X Y : ℂ} (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) :
    Summable (latticeMultiplier X Y) :=
  (latticeMultiplier_norm_summable hX hY).of_norm

theorem latticeMultiplier_tsum {X Y : ℂ} (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) :
    (∑' v : ℤ × ℤ, latticeMultiplier X Y v) =
      (1+X)*(1+Y)/(X*Y*(1-X)*(1-Y)) := by
  simp only [latticeMultiplier,tsum_div_const]
  rw [physical_geometric_lattice_sum hX hY]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Origin counted once, both axes twice, and four open quadrants are all
included by the two genuine integer displacement sums above. -/
theorem latticeMultiplier_tsum_onsite_offsite {X Y : ℂ}
    (hX0 : X ≠ 0) (hY0 : Y ≠ 0) (hX : ‖X‖ < 1) (hY : ‖Y‖ < 1) :
    (∑' v : ℤ × ℤ, latticeMultiplier X Y v) =
      (X*Y)⁻¹+2*(X⁻¹+Y⁻¹)/((1-X)*(1-Y)) := by
  rw [latticeMultiplier_tsum hX hY,full_site_multiplier _ _ hX0 hY0]
  · rw [one_div]
  · exact sub_ne_zero.mpr (fun he => by rw [← he,norm_one] at hX; exact (lt_irrefl _) hX)
  · exact sub_ne_zero.mpr (fun he => by rw [← he,norm_one] at hY; exact (lt_irrefl _) hY)

/-- Every positive N on any interior contour has the required common ratio. -/
theorem coordinate_latticeMultiplier_norm_summable (N : ℕ) (hN : 0 < N)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (q t : Fin N → ℝ) :
    Summable (fun v : ℤ × ℤ =>
      ‖latticeMultiplier (coordinateProduct (angleTuple r q))
        (coordinateProduct (angleTuple r t)) v‖) := by
  apply latticeMultiplier_norm_summable
  · rw [physical_angle_coordinateProduct_norm hr]
    exact pow_lt_one₀ hr hr1 hN.ne'
  · rw [physical_angle_coordinateProduct_norm hr]
    exact pow_lt_one₀ hr hr1 hN.ne'
end
end IsingBulk.Anisotropic.FormFactors
