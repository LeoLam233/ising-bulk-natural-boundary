import IsingBulk.AnisoF002.C03.IsotropicUpperReflection
import IsingBulk.AnisoF002.C03.IsotropicRightPeriodizationOriginal

/-!
# Reflection on the original constrained angular integration boxes

The original [0,2 pi] box is transferred through its exact torus
periodicity and reflected with Lebesgue Jacobian one. The eliminated
angle changes the total constraint from a to -a. Compact mean integrals
reflect their true mean, with the complete normalized physical density.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory
open IsingBulk.AnisoF002.RegularTail.C03

theorem affineConstraintAngles_reflection {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    affineConstraintAngles (-a) (fun i => -x i) = fun i => -affineConstraintAngles a x i := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [affineConstraintAngles_eq_snoc, Fin.snoc_last, Finset.sum_neg_distrib]
    ring
  · simp only [affineConstraintAngles_eq_snoc, Fin.snoc_castSucc]

theorem centeredConstraintAngles_reflection {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    centeredConstraintAngles (-a) (fun i => -x i) = fun i => -centeredConstraintAngles a x i := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [centeredConstraintAngles_eq_snoc, Fin.snoc_last,
      show (fun i : Fin n => -a + -x i) = fun i => -(a + x i) by funext i; ring,
      Finset.sum_neg_distrib]
    ring
  · simp only [centeredConstraintAngles_eq_snoc, Fin.snoc_castSucc]
    ring

theorem regularAngularBox_neg_mem_iff {n : ℕ} (x : Fin n → ℝ) :
    -x ∈ regularAngularBox n ↔ x ∈ regularAngularBox n := by
  change ((fun _ => -Real.pi) ≤ -x ∧ -x ≤ fun _ => Real.pi) ↔
    ((fun _ => -Real.pi) ≤ x ∧ x ≤ fun _ => Real.pi)
  simp only [Pi.le_def, Pi.neg_apply]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> intro i <;>
    linarith only [h₁ i, h₂ i]

theorem regularAngularBox_integral_reflection {n : ℕ} (F : (Fin n → ℝ) → ℂ) :
    (∫ x in regularAngularBox n, F (-x)) = ∫ x in regularAngularBox n, F x := by
  classical
  have hm : MeasurableSet (regularAngularBox n) := measurableSet_Icc
  rw [← integral_indicator hm, ← integral_indicator hm]
  calc
    _ = ∫ x : Fin n → ℝ, (regularAngularBox n).indicator F (-x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      change (if x ∈ regularAngularBox n then F (-x) else 0) =
        if -x ∈ regularAngularBox n then F (-x) else 0
      rw [regularAngularBox_neg_mem_iff]
    _ = _ := integral_neg_eq_self ((regularAngularBox n).indicator F) volume

theorem original_affine_integral_reflection {n : ℕ}
    (F : (Fin (n + 1) → ℝ) → ℂ) (hF : ∀ k θ, F (toroidalTranslation k θ) = F θ) (a : ℝ) :
    (∫ x in angularIntegrationBox n, F (fun i => -affineConstraintAngles a x i)) =
      ∫ x in angularIntegrationBox n, F (affineConstraintAngles (-a) x) := by
  have hnper : ∀ k θ, F (fun i => -toroidalTranslation k θ i) = F (fun i => -θ i) := by
    intro k θ
    have he : (fun i => -toroidalTranslation k θ i) =
        toroidalTranslation (fun i => -k i) (fun i => -θ i) := by
      funext i
      simp only [toroidalTranslation, Int.cast_neg]
      ring
    rw [he, hF]
  rw [angularIntegrationBox_eq_centered_integral _
    (fun k x => by rw [affineConstraintAngles_toroidal_c03, hnper])]
  rw [angularIntegrationBox_eq_centered_integral _
    (fun k x => by rw [affineConstraintAngles_toroidal_c03, hF])]
  have he (x : Fin n → ℝ) : (fun i => -affineConstraintAngles a x i) =
      affineConstraintAngles (-a) (-x) := (affineConstraintAngles_reflection a x).symm
  simp_rw [he]
  exact regularAngularBox_integral_reflection (fun x : Fin n → ℝ => F (affineConstraintAngles (-a) x))

theorem centered_integral_reflection {n : ℕ} (F : (Fin (n + 1) → ℝ) → ℂ) (a : ℝ) :
    (∫ x : Fin n → ℝ, F (fun i => -centeredConstraintAngles a x i)) =
      ∫ x : Fin n → ℝ, F (centeredConstraintAngles (-a) x) := by
  have he (x : Fin n → ℝ) : (fun i => -centeredConstraintAngles a x i) =
      centeredConstraintAngles (-a) (-x) := (centeredConstraintAngles_reflection a x).symm
  simp_rw [he]
  exact integral_neg_eq_self (fun x : Fin n → ℝ => F (centeredConstraintAngles (-a) x)) volume

/-- Literal full normalized particle integral with a real angular
weight. This leaves every original one-body, pair, kernel and factorial
factor inside the physical density. -/
def actualWeightedParticleIntegral {n : ℕ} (η τ ξ : ℝ) (σ : ℂ)
    (g : (Fin (n + 1) → ℝ) → ℂ) (a : ℝ) (s : ℂ) : ℂ :=
  ∫ x in angularIntegrationBox n, g (affineConstraintAngles a x) *
    homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ) (ξ, affineConstraintAngles a x)

theorem actualWeightedParticleIntegral_reflection {n : ℕ} (η τ ξ : ℝ) (s σ : ℂ)
    (g : (Fin (n + 1) → ℝ) → ℂ) (hg : ∀ k θ, g (toroidalTranslation k θ) = g θ) (a : ℝ) :
    actualWeightedParticleIntegral η τ ξ σ (fun θ => g (fun i => -θ i)) a s =
      actualWeightedParticleIntegral η τ ξ σ g (-a) s := by
  let F : (Fin (n + 1) → ℝ) → ℂ := fun θ => g θ *
    homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ) (ξ, θ)
  have hF : ∀ k θ, F (toroidalTranslation k θ) = F θ := by
    intro k θ
    dsimp only [F]
    rw [hg, homotopyPulledDensity_toroidal η τ ξ _ (isotropicBarePhysicalDensity_periodic s σ)]
  have hh := original_affine_integral_reflection F hF a
  simpa only [F, actual_physical_density_reflection, actualWeightedParticleIntegral] using hh

theorem actualWeightedParticleIntegral_reflection_jets {n : ℕ} (η τ ξ : ℝ) (σ : ℂ)
    (g : (Fin (n + 1) → ℝ) → ℂ) (hg : ∀ k θ, g (toroidalTranslation k θ) = g θ)
    (a : ℝ) (j : ℕ) (s : ℂ) :
    iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ (fun θ => g (fun i => -θ i)) a) s =
      iteratedDeriv j (actualWeightedParticleIntegral η τ ξ σ g (-a)) s := by
  have he := funext (fun z => actualWeightedParticleIntegral_reflection η τ ξ z σ g hg a)
  rw [he]

theorem actual_compact_physical_integral_reflection {n : ℕ} (η τ ξ : ℝ) (s σ : ℂ)
    (g : (Fin (n + 1) → ℝ) → ℂ) (a : ℝ) :
    (∫ x : Fin n → ℝ, g (fun i => -centeredConstraintAngles a x i) *
      homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ) (ξ, centeredConstraintAngles a x)) =
      ∫ x : Fin n → ℝ, g (centeredConstraintAngles (-a) x) *
        homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ)
          (ξ, centeredConstraintAngles (-a) x) := by
  have hh := centered_integral_reflection (fun θ => g θ *
    homotopyPulledDensity η τ (isotropicBarePhysicalDensity s σ) (ξ, θ)) a
  simpa only [actual_physical_density_reflection] using hh

end IsingBulk.AnisoF002.Isotropic
