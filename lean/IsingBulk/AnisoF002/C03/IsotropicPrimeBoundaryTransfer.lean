import IsingBulk.AnisoF002.C03.IsotropicOriginalBoundaryTransfer
import IsingBulk.AnisoF002.C03.IsotropicPrimeDensity

/-!
# Separate prime families and every finite physical frontier

Positive odd and even obstructions use prime angles in (0,pi/2).
Signed odd obstructions use pi minus prime angles in (pi/2,pi).
These two families are kept separate. Their actual density and the exact
full-series reflection give both original normalized and physical domains.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology
open Set Filter IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors

def isotropicPositivePrimeAngles : Set ℝ :=
  isotropicPrimeAngles ∩ Ioo (0 : ℝ) (Real.pi / 2)

def isotropicSignedPrimeAngles : Set ℝ :=
  (fun α : ℝ => Real.pi - α) '' (isotropicPrimeAngles ∩ Ioo (Real.pi / 2) Real.pi)

theorem isotropicPositivePrimeAngles_subset :
    isotropicPositivePrimeAngles ⊆ Ioo (0 : ℝ) (Real.pi / 2) := fun _ h => h.2

theorem isotropicSignedPrimeAngles_subset :
    isotropicSignedPrimeAngles ⊆ Ioo (0 : ℝ) (Real.pi / 2) := by
  rintro α ⟨β, hβ, rfl⟩
  constructor <;> linarith [hβ.2.1, hβ.2.2]

theorem isotropicPositivePrimeAngles_closure {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    α ∈ closure isotropicPositivePrimeAngles := by
  exact isotropicPrimeAngles_local_closure
    ⟨hα.1, by linarith [hα.2, Real.pi_pos]⟩ isOpen_Ioo hα

theorem isotropicSignedPrimeAngles_closure {α : ℝ}
    (hα : α ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    α ∈ closure isotropicSignedPrimeAngles := by
  have hβ : Real.pi - α ∈ Ioo (Real.pi / 2) Real.pi := by
    constructor <;> linarith [hα.1, hα.2]
  have hh := isotropicPrimeAngles_local_closure
    (show Real.pi - α ∈ Ioo (0 : ℝ) Real.pi from
      ⟨by linarith [hβ.1, Real.pi_pos], hβ.2⟩) isOpen_Ioo hβ
  have hc : ContinuousAt (fun β : ℝ => Real.pi - β) (Real.pi - α) := by fun_prop
  simpa only [sub_sub_cancel, isotropicSignedPrimeAngles] using mem_closure_image hc hh

def isotropicReflectedAngleFamily (P Q : Set ℝ) : Set ℝ :=
  P ∪ (fun α : ℝ => Real.pi - α) '' Q

theorem isotropicReflectedAngleFamily_subset {P Q : Set ℝ}
    (hP : P ⊆ Ioo (0 : ℝ) (Real.pi / 2))
    (hQ : Q ⊆ Ioo (0 : ℝ) (Real.pi / 2)) :
    isotropicReflectedAngleFamily P Q ⊆ Ioo (0 : ℝ) Real.pi := by
  rintro α (h | ⟨β, hβ, rfl⟩)
  · exact ⟨(hP h).1, by linarith [(hP h).2, Real.pi_pos]⟩
  · constructor <;> linarith [(hQ hβ).1, (hQ hβ).2, Real.pi_pos]

theorem isotropicReflectedAngleFamily_closure {P Q : Set ℝ}
    (hP : Ioo (0 : ℝ) (Real.pi / 2) ⊆ closure P)
    (hQ : Ioo (0 : ℝ) (Real.pi / 2) ⊆ closure Q)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) Real.pi) (hne : α ≠ Real.pi / 2) :
    α ∈ closure (isotropicReflectedAngleFamily P Q) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact closure_mono (show P ⊆ isotropicReflectedAngleFamily P Q from subset_union_left)
      (hP ⟨hα.1, hlt⟩)
  · have hβ : Real.pi - α ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
      constructor <;> linarith [hα.2]
    have hc : ContinuousAt (fun β : ℝ => Real.pi - β) (Real.pi - α) := by fun_prop
    have hh : α ∈ closure ((fun β : ℝ => Real.pi - β) '' Q) := by
      simpa only [sub_sub_cancel] using mem_closure_image hc (hQ hβ)
    exact closure_mono (show (fun β : ℝ => Real.pi - β) '' Q ⊆
      isotropicReflectedAngleFamily P Q from subset_union_right) hh

theorem isotropic_high_boundaries_of_prime_radial {J : ℝ} (hJ : 0 < J)
    (hpositive : ∀ α ∈ isotropicPositivePrimeAngles,
      ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 0 0 1) α)
    (hsigned : ∀ α ∈ isotropicSignedPrimeAngles,
      ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 0 Real.pi (-1)) α) :
    NaturalBoundaryOn (omegaH 1) (highNormalizedBulk 1) ∧
      NaturalBoundaryOn (omegaH 1) (highPhysicalBulk J 1) := by
  let A := isotropicReflectedAngleFamily isotropicPositivePrimeAngles isotropicSignedPrimeAngles
  have hA : A ⊆ Ioo (0 : ℝ) Real.pi :=
    isotropicReflectedAngleFamily_subset isotropicPositivePrimeAngles_subset isotropicSignedPrimeAngles_subset
  have hd : ∀ α ∈ Ioo (0 : ℝ) Real.pi, α ≠ Real.pi / 2 → α ∈ closure A :=
    fun _ hα hne => isotropicReflectedAngleFamily_closure
      (fun _ h => isotropicPositivePrimeAngles_closure h)
      (fun _ h => isotropicSignedPrimeAngles_closure h) hα hne
  have hno : ∀ α ∈ A, ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 0 0 1) α := by
    rintro α (h | ⟨β, hβ, rfl⟩)
    · exact hpositive α h
    · have hb := isotropicSignedPrimeAngles_subset hβ
      exact fun hg => hsigned β hβ (isotropic_odd_radial_germ_reflection
        ⟨hb.1, by linarith [hb.2, Real.pi_pos]⟩ hg)
  exact ⟨isotropic_high_normalized_boundary_of_dense_radial hA hd hno,
    isotropic_high_physical_boundary_of_dense_radial hJ hA hd hno⟩

theorem isotropic_low_boundaries_of_prime_radial {J : ℝ} (hJ : 0 < J)
    (hpositive : ∀ α ∈ isotropicPositivePrimeAngles,
      ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 1 0 1) α) :
    NaturalBoundaryOn (omegaL 1) (lowNormalizedBulk 1) ∧
      NaturalBoundaryOn (omegaL 1) (lowPhysicalBulk J 1) := by
  let A := isotropicReflectedAngleFamily isotropicPositivePrimeAngles isotropicPositivePrimeAngles
  have hA : A ⊆ Ioo (0 : ℝ) Real.pi :=
    isotropicReflectedAngleFamily_subset isotropicPositivePrimeAngles_subset isotropicPositivePrimeAngles_subset
  have hd : ∀ α ∈ Ioo (0 : ℝ) Real.pi, α ≠ Real.pi / 2 → α ∈ closure A :=
    fun _ hα hne => isotropicReflectedAngleFamily_closure
      (fun _ h => isotropicPositivePrimeAngles_closure h)
      (fun _ h => isotropicPositivePrimeAngles_closure h) hα hne
  have hno : ∀ α ∈ A, ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 1 0 1) α := by
    rintro α (h | ⟨β, hβ, rfl⟩)
    · exact hpositive α h
    · have hb := isotropicPositivePrimeAngles_subset hβ
      exact fun hg => hpositive β hβ (isotropic_even_radial_germ_reflection
        ⟨hb.1, by linarith [hb.2, Real.pi_pos]⟩ hg)
  exact ⟨isotropic_low_normalized_boundary_of_dense_radial hA hd hno,
    isotropic_low_physical_boundary_of_dense_radial hJ hA hd hno⟩

end IsingBulk.AnisoF002.Isotropic
