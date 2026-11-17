import IsingBulk.AnisoF002.C03.IsotropicPrimeNoncancellation
import IsingBulk.AnisoF002.C03.IsotropicPrimeBoundaryTransfer

/-!
# The four complete original isotropic natural-boundary conclusions

The three radial noncancellation mechanisms are the independently proved
F002 complete physical series. Prime density, exact physical coordinates,
the chosen physical prefactors and closure at every finite frontier point
are all discharged. No additional analytic or physical hypothesis occurs.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors

theorem isotropic_positive_prime_family_no_germ :
    ∀ α ∈ isotropicPositivePrimeAngles,
      ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 0 0 1) α := by
  rintro α ⟨⟨a, p, hp7, hp, _, _, ha, rfl⟩, hα⟩
  exact isotropic_positive_prime_no_radial_germ hp hp7 ha hα.1 hα.2

theorem isotropic_even_prime_family_no_germ :
    ∀ α ∈ isotropicPositivePrimeAngles,
      ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 1 0 1) α := by
  rintro α ⟨⟨a, p, hp7, hp, _, _, ha, rfl⟩, hα⟩
  exact isotropic_even_prime_no_radial_germ hp hp7 ha hα.1 hα.2

theorem isotropic_signed_prime_family_no_germ :
    ∀ α ∈ isotropicSignedPrimeAngles,
      ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 0 Real.pi (-1)) α := by
  rintro α ⟨β, ⟨⟨a, p, hp7, hp, _, _, ha, rfl⟩, hβ⟩, rfl⟩
  exact isotropic_negative_prime_no_radial_germ hp hp7 ha
    (by linarith [hβ.2]) (by linarith [hβ.1])

theorem isotropic_high_normalized_naturalBoundary :
    NaturalBoundaryOn (omegaH 1) (highNormalizedBulk 1) :=
  (isotropic_high_boundaries_of_prime_radial (J := 1) (by norm_num)
    isotropic_positive_prime_family_no_germ isotropic_signed_prime_family_no_germ).1

theorem isotropic_low_normalized_naturalBoundary :
    NaturalBoundaryOn (omegaL 1) (lowNormalizedBulk 1) :=
  (isotropic_low_boundaries_of_prime_radial (J := 1) (by norm_num)
    isotropic_even_prime_family_no_germ).1

theorem isotropic_high_physical_naturalBoundary {J : ℝ} (hJ : 0 < J) :
    NaturalBoundaryOn (omegaH 1) (highPhysicalBulk J 1) :=
  (isotropic_high_boundaries_of_prime_radial hJ
    isotropic_positive_prime_family_no_germ isotropic_signed_prime_family_no_germ).2

theorem isotropic_low_physical_naturalBoundary {J : ℝ} (hJ : 0 < J) :
    NaturalBoundaryOn (omegaL 1) (lowPhysicalBulk J 1) :=
  (isotropic_low_boundaries_of_prime_radial hJ isotropic_even_prime_family_no_germ).2

end IsingBulk.AnisoF002.Isotropic
