import IsingBulk.HT.Final.PublishedPhysicalIdentification
import IsingBulk.HT.Final.FullNaturalBoundary

/-! Physical natural-boundary packaging. The analytic boundary obstruction and
actual angular identification are separate proved imports. Only the literal
published statistical-mechanical representation remains an external premise. -/
namespace IsingBulk.HT.Final
noncomputable section

/-- Full HT physical-germ natural-boundary theorem, conditional only on the
precisely stated published statistical-mechanical angular expansion.
The constructed analytic germ agrees with the physical susceptibility
throughout `0 < x < 1`; every unit-circle point obstructs continuation.
There is no FIRST, TAIL, Fourier, summability or continuation premise. -/
theorem publishedPhysicalSusceptibility_germ_natural_boundary
    {J : ℝ} (hJ : 0 < J) {chi : ℂ → ℂ}
    (hpub : PublishedAngularSusceptibilityRepresentation J chi) :
    AnalyticOnNhd ℂ (interiorPhysicalSusceptibility J) {s : ℂ | ‖s‖ < 1} ∧
      (∀ x : ℝ, 0 < x → x < 1 →
        chi (x:ℂ) = interiorPhysicalSusceptibility J (x:ℂ)) ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ¬ HasInteriorExtension (interiorPhysicalSusceptibility J) z := by
  have hrep := publishedAngularSusceptibility_to_contour hpub
  exact ⟨interiorPhysicalSusceptibility_analyticOn hJ,
    fun _ hx hx1 => physicalSusceptibility_real_interval hJ hrep hx hx1,
    interiorPhysicalSusceptibility_unit_circle_no_extension hJ⟩

/-- If an exact analytic continuation `chi` is already given on the disk,
the no-extension conclusion applies to that function itself. The analyticity
premise is explicit and is not required by the preceding germ theorem. -/
theorem publishedPhysicalSusceptibility_unit_circle_no_extension
    {J : ℝ} (hJ : 0 < J) {chi : ℂ → ℂ}
    (hchi : AnalyticOnNhd ℂ chi {s : ℂ | ‖s‖ < 1})
    (hpub : PublishedAngularSusceptibilityRepresentation J chi) :
    ∀ z : ℂ, ‖z‖ = 1 → ¬ HasInteriorExtension chi z :=
  physicalSusceptibility_unit_circle_no_extension hJ hchi
    (publishedAngularSusceptibility_to_contour hpub)

end
end IsingBulk.HT.Final
