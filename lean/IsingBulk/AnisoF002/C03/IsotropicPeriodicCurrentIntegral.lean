import IsingBulk.AnisoF002.C03.IsotropicConstrainedCurrent
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Integrating the true angular current, including coincidence exceptions

This is an ordinary Lebesgue box identity. Opposite periodic faces
cancel, and a countable exceptional set contributes no volume term.
The same statement applies to compactly supported fluxes whose face
values vanish. Continuity of the flux and integrability are retained
as substantive hypotheses for the later actual collision estimates.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Filter MeasureTheory

theorem periodic_box_divergence_zero {n : ℕ} (a b : Fin (n + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℂ)
    (F' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℂ)
    (S : Set (Fin (n + 1) → ℝ)) (hS : S.Countable)
    (hF : ∀ i, ContinuousOn (F i) (Icc a b))
    (hD : ∀ x ∈ (Set.univ.pi fun i => Ioo (a i) (b i)) \ S,
      ∀ i, HasFDerivAt (F i) (F' i x) x)
    (hI : IntegrableOn (fun x => ∑ i, F' i x (Pi.single i 1)) (Icc a b) volume)
    (hfaces : ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      F i (i.insertNth (b i) y) = F i (i.insertNth (a i) y)) :
    (∫ x in Icc a b, ∑ i, F' i x (Pi.single i 1)) = 0 := by
  rw [integral_divergence_of_hasFDerivAt_off_countable' a b hab F F' S hS hF hD hI]
  apply Finset.sum_eq_zero
  intro i _
  rw [setIntegral_congr_fun measurableSet_Icc (hfaces i), sub_self]

theorem compact_face_divergence_zero {n : ℕ} (a b : Fin (n + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℂ)
    (F' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℂ)
    (S : Set (Fin (n + 1) → ℝ)) (hS : S.Countable)
    (hF : ∀ i, ContinuousOn (F i) (Icc a b))
    (hD : ∀ x ∈ (Set.univ.pi fun i => Ioo (a i) (b i)) \ S,
      ∀ i, HasFDerivAt (F i) (F' i x) x)
    (hI : IntegrableOn (fun x => ∑ i, F' i x (Pi.single i 1)) (Icc a b) volume)
    (hfaces : ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      F i (i.insertNth (b i) y) = 0 ∧ F i (i.insertNth (a i) y) = 0) :
    (∫ x in Icc a b, ∑ i, F' i x (Pi.single i 1)) = 0 :=
  periodic_box_divergence_zero a b hab F F' S hS hF hD hI
    (fun i y hy => (hfaces i y hy).1.trans (hfaces i y hy).2.symm)

/-- A current identity valid off the actual exceptional set gives the
literal integrated derivative identity. Integrability of its divergence
is deduced from the two physical densities, rather than assumed again. -/
theorem integrated_current_off_countable {n : ℕ} (a b : Fin (n + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℂ)
    (F' : Fin (n + 1) → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℂ)
    (S : Set (Fin (n + 1) → ℝ)) (hS : S.Countable)
    (hF : ∀ i, ContinuousOn (F i) (Icc a b))
    (hD : ∀ x ∈ (Set.univ.pi fun i => Ioo (a i) (b i)) \ S,
      ∀ i, HasFDerivAt (F i) (F' i x) x)
    (hfaces : ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      F i (i.insertNth (b i) y) = F i (i.insertNth (a i) y))
    (timeDensity nextDensity : (Fin (n + 1) → ℝ) → ℂ)
    (htime : IntegrableOn timeDensity (Icc a b) volume)
    (hnext : IntegrableOn nextDensity (Icc a b) volume)
    (hcurrent : ∀ x ∈ Icc a b, x ∉ S →
      timeDensity x - (∑ i, F' i x (Pi.single i 1)) = nextDensity x) :
    (∫ x in Icc a b, timeDensity x) = ∫ x in Icc a b, nextDensity x := by
  have he : (fun x => ∑ i, F' i x (Pi.single i 1)) =ᵐ[volume.restrict (Icc a b)]
      (fun x => timeDensity x - nextDensity x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      hS.ae_notMem (volume.restrict (Icc a b))] with x hx hxs
    linear_combination -(hcurrent x hx hxs)
  have hI : IntegrableOn (fun x => ∑ i, F' i x (Pi.single i 1)) (Icc a b) volume :=
    (htime.sub hnext).congr he.symm
  have hz := periodic_box_divergence_zero a b hab F F' S hS hF hD hI hfaces
  rw [integral_congr_ae he, integral_sub htime hnext] at hz
  exact sub_eq_zero.mp hz

end IsingBulk.AnisoF002.Isotropic
