import IsingBulk.HT.Contour.PhysicalAngularIdentification
import IsingBulk.HT.Final.PublishedAngularInput
import IsingBulk.HT.Final.PhysicalLatticeSeries
import IsingBulk.HT.Final.PhysicalRealInterval

/-! Exact published angular identification, independent of the boundary proof.

The only external physical premise is the literal real odd-particle angular
expansion in `PublishedAngularInput`. Its full-lattice Fourier attachment,
absolute lattice convergence, angular-to-contour identity and odd-particle
convergence are proved dependencies. FIRST, TAIL and boundary obstruction
are assembled separately in PublishedPhysicalTheorem. The conditional
identification is not an unconditional construction of the Gibbs state. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open scoped BigOperators

/-- The published angular odd series is absolutely convergent on the real
physical interval because its actual coefficients equal the normally
convergent contour coefficients. Convergence is not a physical input. -/
theorem physicalAngularOdd_norm_summable {t : ℝ} (ht : 1 < t) :
    Summable (fun n : ℕ => ‖physicalAngularCoefficient (2*n) t‖) := by
  have hS := physical_real_trace_gt_two ht
  obtain ⟨hr,hr1,hm⟩ := rightCanonicalRadius_admissible hS
  have hs : Summable (fun n : ℕ => ‖rightFullCoefficient (2*n+1) (t:ℂ)‖) := by
    simpa only [iteratedDeriv_zero] using rightFullOdd_derivative_summable 0 hS
  apply hs.congr
  intro n
  rw [physicalAngularCoefficient_eq_standardFormFactor (2*n) ht hr hr1 hm,
    rightFullCoefficient_eq_fixed_radius (2*n+1) (by omega) hr hr1 hm]

/-- A concrete witness for the published bulk predicate, independent of
any physical representation hypothesis. This identifies the constructed
analytic germ with the actual angular series on the entire physical interval
and ensures that the external input predicate is not vacuous. -/
theorem interiorFullBulk_publishedAngularRepresentation :
    PublishedAngularBulkRepresentation interiorFullBulk := by
  intro x hx hx1
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hxi : 1 < x⁻¹ := (one_lt_inv₀ hx).mpr hx1
  have hS := physical_real_trace_gt_two hxi
  obtain ⟨hr,hr1,hm⟩ := rightCanonicalRadius_admissible hS
  have hS' : 2 < (sourceS ((x:ℂ)⁻¹)).re := by
    simpa only [Complex.ofReal_inv] using hS
  have hm' : 1+(rightCanonicalRadius ((x⁻¹:ℝ):ℂ))⁻¹ <
      (sourceS ((x:ℂ)⁻¹)).re := by
    simpa only [Complex.ofReal_inv] using hm
  have hP : exteriorPrefactor ((x:ℂ)⁻¹) = interiorPrefactor (x:ℂ) := by
    simpa only [inv_inv] using (interiorPrefactor_inv ((x:ℂ)⁻¹)).symm
  have hseries :
      fixedOddFullSeries (rightCanonicalRadius ((x⁻¹:ℝ):ℂ)) ((x:ℂ)⁻¹) =
        publishedAngularOddSeries x⁻¹ := by
    apply tsum_congr
    intro n
    simpa only [oddFullCoefficient,Complex.ofReal_inv] using
      (physicalAngularCoefficient_eq_standardFormFactor (2*n) hxi hr hr1 hm).symm
  rw [interiorFullBulk_eq_exterior hx0,exteriorFullBulk,
    exteriorOddSeries_eq_right hS',rightFullOddSeries_eq_fixed_radius hr hr1 hm',
    hP,hseries]

/-- A concrete susceptibility witness for the exact published predicate.
It is constructed internally, rather than postulated as an inhabitant of
the external physical interface. -/
theorem interiorPhysicalSusceptibility_publishedAngularRepresentation
    {J : ℝ} (hJ : 0 < J) :
    PublishedAngularSusceptibilityRepresentation J
      (interiorPhysicalSusceptibility J) := by
  intro x hx hx1
  have hb := (IsingBulk.Final.inverseTemperatureBranch_regular
    (show 0 < (x:ℂ).re by simpa only [Complex.ofReal_re] using hx) hJ).2
  apply (div_eq_iff hb).2
  rw [interiorPhysicalSusceptibility,
    interiorFullBulk_publishedAngularRepresentation x hx hx1]
  ring

/-- The exact published angular input implies the older contour-normalized
interface. Every analytic attachment is discharged by an actual theorem. -/
theorem publishedAngularBulk_to_contour {X : ℂ → ℂ}
    (hpub : PublishedAngularBulkRepresentation X) :
    RealFullBulkRepresentation X := by
  intro x hx hx1
  have hxi : 1 < x⁻¹ := (one_lt_inv₀ hx).mpr hx1
  obtain ⟨r₀,hr₀,hr₀1,hm₀⟩ := physical_real_common_radius hxi
  refine ⟨r₀,hr₀,hr₀1,?_⟩
  intro r hr hr1
  have hrpos : 0 < r := hr₀.trans hr
  have hm := hm₀ r hr hr1
  have hcoeff (n : ℕ) :
      physicalAngularCoefficient (2*n) x⁻¹ =
        oddFullCoefficient n r ((x:ℂ)⁻¹) := by
    simpa only [oddFullCoefficient,Complex.ofReal_inv] using
      physicalAngularCoefficient_eq_standardFormFactor (2*n) hxi hrpos hr1 hm
  refine ⟨(physicalAngularOdd_norm_summable hxi).of_norm.congr hcoeff,?_⟩
  rw [hpub x hx hx1]
  congr 1
  exact tsum_congr hcoeff

/-- No extra input is required to pass from the literal angular physical
susceptibility representation to the contour-normalized representation. -/
theorem publishedAngularSusceptibility_to_contour {J : ℝ} {chi : ℂ → ℂ}
    (hpub : PublishedAngularSusceptibilityRepresentation J chi) :
    PhysicalSusceptibilityRepresentation J chi :=
  publishedAngularBulk_to_contour hpub

end
end IsingBulk.HT.Final
