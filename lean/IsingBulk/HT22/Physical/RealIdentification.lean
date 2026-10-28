import IsingBulk.HT22.Physical.Angular
import IsingBulk.HT.Contour.PhysicalAngularIdentification
import IsingBulk.HT.Final.PublishedAngularInput

/-!
# HT22's actual angular coefficients and the real full lattice

This is an exact identification with the published physical objects, not a
new physical premise. Every lattice site and every positive odd particle
count is retained. Pointwise-in-particle absolute lattice convergence is
proved here; joint lattice/particle absolute convergence is not asserted.
-/
namespace IsingBulk.HT22.Physical
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.HT.Final
open scoped BigOperators

/-- An explicit real contour radius, common to every particle order. -/
def realContourRadius (t : ℝ) : ℝ := 2/(t+t⁻¹)

theorem realContourRadius_admissible {t : ℝ} (ht : 1 < t) :
    0 < realContourRadius t ∧ realContourRadius t < 1 ∧
      1 + (realContourRadius t)⁻¹ < (sourceS (t:ℂ)).re := by
  have hS := physical_trace_gt_two ht
  have hS0 : 0 < t+t⁻¹ := lt_trans (by norm_num) hS
  refine ⟨div_pos (by norm_num) hS0, (div_lt_one hS0).mpr hS, ?_⟩
  simp only [realContourRadius, inv_div, sourceS, Complex.add_re,
    Complex.ofReal_re, ← Complex.ofReal_inv]
  linarith

/-- The literal N-particle coefficient is the sum over the whole square lattice. -/
theorem coefficient_eq_fullLattice_tsum {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 1 < t) :
    coefficient N (t:ℂ) =
      ∑' v : ℤ × ℤ, physicalFullLatticeCoefficient N t v := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨hr, hr1, hm⟩ := realContourRadius_admissible ht
  rw [coefficient_eq_published_succ n ht]
  exact physicalAngularCoefficient_eq_fullLattice_tsum n ht hr hr1 hm

/-- Absolute lattice summability at each actual positive particle number. -/
theorem fullLattice_norm_summable {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 1 < t) :
    Summable (fun v : ℤ × ℤ => ‖physicalFullLatticeCoefficient N t v‖) := by
  obtain ⟨hr, hr1, hm⟩ := realContourRadius_admissible ht
  exact (physicalFullLatticeCoefficient_summable_eq_standardFormFactor
    N hN ht hr hr1 hm).1

/-- The lattice origin is present, not discarded as an offsite term. -/
theorem fullLattice_origin (N : ℕ) (t : ℝ) :
    physicalFullLatticeCoefficient N t ((0, 0) : ℤ × ℤ) =
      physicalLatticeCoefficient N t 0 0 := by
  simp only [physicalFullLatticeCoefficient, Int.natAbs_zero]

/-- Expose the origin addend in the actual convergent coefficient. This does
not claim that an individual particle's origin contribution equals one. -/
theorem coefficient_eq_origin_add_offOrigin {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 1 < t) :
    coefficient N (t:ℂ) = physicalLatticeCoefficient N t 0 0 +
      ∑' v : ℤ × ℤ, if v = (0, 0) then 0 else physicalFullLatticeCoefficient N t v := by
  rw [coefficient_eq_fullLattice_tsum hN ht]
  simpa only [fullLattice_origin] using
    (fullLattice_norm_summable hN ht).of_norm.tsum_eq_add_tsum_ite (0, 0)

/-- Complete series: n runs over all naturals, hence N over all positive odds. -/
def oddSeries (t : ℂ) : ℂ := ∑' n : ℕ, coefficient (2*n+1) t

/-- Equality of literal sums; convergence is deliberately not hidden in `tsum`. -/
theorem oddSeries_real_eq_published {t : ℝ} (ht : 1 < t) :
    oddSeries (t:ℂ) = publishedAngularOddSeries t := by
  apply tsum_congr
  intro n
  exact coefficient_odd_eq_published n ht

theorem oddSeries_real_eq_fullLattice {t : ℝ} (ht : 1 < t) :
    oddSeries (t:ℂ) =
      ∑' n : ℕ, ∑' v : ℤ × ℤ, physicalFullLatticeCoefficient (2*n+1) t v := by
  apply tsum_congr
  intro n
  exact coefficient_eq_fullLattice_tsum (by omega) ht

/-- Beta-free F001 source in the exterior coordinate, on its prescribed branch. -/
def exteriorBulk (t : ℂ) : ℂ := exteriorPrefactor t * oddSeries t

/-- The genuine punctured interior formula. Removal of s=0 is a separate duty. -/
def puncturedInteriorBulk (s : ℂ) : ℂ := interiorPrefactor s * oddSeries s⁻¹

theorem puncturedInteriorBulk_eq_exterior (s : ℂ) :
    puncturedInteriorBulk s = exteriorBulk s⁻¹ := by
  unfold puncturedInteriorBulk exteriorBulk
  rw [← interiorPrefactor_inv]
  simp only [inv_inv]

/-- The sole physical hypothesis remains exactly the published real one. -/
theorem publishedBulk_eq_F001_real {X : ℂ → ℂ}
    (hpub : PublishedAngularBulkRepresentation X) {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1) :
    X (x:ℂ) = puncturedInteriorBulk (x:ℂ) := by
  rw [hpub x hx hx1]
  unfold puncturedInteriorBulk
  rw [← Complex.ofReal_inv, oddSeries_real_eq_published ((one_lt_inv₀ hx).mpr hx1)]

/-- Restore the physical beta, without any complex physical-input premise. -/
theorem publishedSusceptibility_eq_F001_real {J : ℝ} (hJ : 0 < J)
    {chi : ℂ → ℂ} (hpub : PublishedAngularSusceptibilityRepresentation J chi)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    chi (x:ℂ) = IsingBulk.Final.inverseTemperatureBranch J (x:ℂ) *
      puncturedInteriorBulk (x:ℂ) := by
  have he := publishedBulk_eq_F001_real hpub hx hx1
  have hb := (IsingBulk.Final.inverseTemperatureBranch_regular
    (show 0 < (x:ℂ).re by simpa only [Complex.ofReal_re] using hx) hJ).2
  have he' := (div_eq_iff hb).mp he
  simpa only [mul_comm] using he'

end
end IsingBulk.HT22.Physical
