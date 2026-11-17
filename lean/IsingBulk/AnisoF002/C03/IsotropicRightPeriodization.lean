import IsingBulk.AnisoF002.C03.IsotropicCompactRightCutoff
import IsingBulk.AnisoF002.C03.IsotropicFullPhysicalHomotopy
import IsingBulk.AnisoF002.C03.IsotropicConstrainedMeans
import IsingBulk.AnisoF002.C03.RegularWindingTorusMeasure
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Exact finite periodization of the actual compact right cutoff

Only the eliminated last angle is shifted. The independent angles keep
their original Lebesgue measure. The full periodic density is the exact
finite sum of compact integer lifts; the admissible means are the same
ones used by the complete coarea estimates.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory
open IsingBulk.AnisoF002.RegularTail.C03

/-- A scalar periodic cutoff has exactly one possibly nonzero compact
lift. Endpoint zeros make the identity valid everywhere, not only a.e. -/
theorem compactRightCutoff_unique_lift {b δ ρ : ℝ} (h : RightCutoffGeometry b δ ρ) (x : ℝ) :
    ∃ l₀ : ℤ,
      compactRightCutoff b δ ρ (x + (l₀ : ℝ) * (2 * Real.pi)) = periodicRightCutoff b δ ρ x ∧
      ∀ l : ℤ, l ≠ l₀ → compactRightCutoff b δ ρ (x + (l : ℝ) * (2 * Real.pi)) = 0 := by
  obtain ⟨l₀, hl₀, huniq⟩ := existsUnique_add_zsmul_mem_Ioc Real.two_pi_pos x (-Real.pi)
  have hfund : x + (l₀ : ℝ) * (2 * Real.pi) ∈ Icc (-Real.pi) Real.pi := by
    simp only [mem_Ioc, zsmul_eq_mul] at hl₀
    exact ⟨hl₀.1.le, by linarith only [hl₀.2]⟩
  refine ⟨l₀, ?_, ?_⟩
  · rw [compactRightCutoff_eq_periodic h hfund]
    exact (periodicRightCutoff_periodic b δ ρ).int_mul l₀ x
  · intro l hl
    by_contra hn
    have hlo : -Real.pi < x + (l : ℝ) * (2 * Real.pi) := by
      by_contra hh
      exact hn (compactRightCutoff_zero_outside h (Or.inl (le_of_not_gt hh)))
    have hup : x + (l : ℝ) * (2 * Real.pi) < Real.pi := by
      by_contra hh
      exact hn (compactRightCutoff_zero_outside h (Or.inr (le_of_not_gt hh)))
    apply hl
    exact huniq l (by simpa only [mem_Ioc, zsmul_eq_mul,
      show -Real.pi + 2 * Real.pi = Real.pi by ring] using And.intro hlo hup.le)

theorem affineConstraintAngles_sum_c03 {n : ℕ} (a : ℝ) (x : Fin n → ℝ) :
    (∑ i, affineConstraintAngles a x i) = a := by
  rw [affineConstraintAngles_eq_snoc, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

theorem affineConstraintAngles_last_period {n : ℕ} (a : ℝ) (x : Fin n → ℝ) (l : ℤ) :
    affineConstraintAngles (2 * Real.pi * l + a) x =
      toroidalTranslation (Pi.single (Fin.last n) l) (affineConstraintAngles a x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [affineConstraintAngles_eq_snoc, Fin.snoc_last, toroidalTranslation, Pi.single_eq_same]
    ring
  · simp [affineConstraintAngles_eq_snoc, toroidalTranslation, Fin.castSucc_ne_last]

/-- The compact full product itself determines an admissible constrained
mean; no winding class is discarded by convention. -/
theorem compactRightProduct_admissible_lift {b δ ρ β : ℝ} (h : RightCutoffGeometry b δ ρ)
    (hδ : δ ≤ β) (hρ : ρ + δ / 2 ≤ β) {n : ℕ} (a : ℝ) (x : Fin n → ℝ) (l : ℤ)
    (hn : compactRightProduct b δ ρ (n + 1) (affineConstraintAngles (2 * Real.pi * l + a) x) ≠ 0) :
    l ∈ admissibleRightLifts (n + 1) b β a := by
  have ht := compactRightProduct_weighted_tsupport h (fun _ : (Fin (n + 1) → ℝ) => (1 : ℂ))
    (subset_closure (show (1 : ℂ) * compactRightProduct b δ ρ (n + 1)
      (affineConstraintAngles (2 * Real.pi * l + a) x) ≠ 0 by simpa only [one_mul] using hn))
  have hlo := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
    show -b - β ≤ affineConstraintAngles (2 * Real.pi * l + a) x i by linarith only [(ht i).1, hδ])
  have hup := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
    (ht i).2.trans hρ)
  rw [affineConstraintAngles_sum_c03, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hlo hup
  exact (admissibleRightLifts_mem_iff (n + 1) b β a l).mpr ⟨hlo, hup⟩

/-- Pointwise finite periodization on the unchanged independent angular
box. Every full periodic factor is carried along with the compact weight. -/
theorem rightProduct_finite_periodization {b δ ρ β : ℝ} (h : RightCutoffGeometry b δ ρ)
    (hδ : δ ≤ β) (hρ : ρ + δ / 2 ≤ β) {n : ℕ}
    (F : (Fin (n + 1) → ℝ) → ℂ)
    (hF : ∀ k θ, F (toroidalTranslation k θ) = F θ)
    (a : ℝ) (x : Fin n → ℝ) (hx : x ∈ regularAngularBox n) :
    rightCutoffProduct b δ ρ (n + 1) (affineConstraintAngles a x) * F (affineConstraintAngles a x) =
      ∑ l ∈ admissibleRightLifts (n + 1) b β a,
        compactRightProduct b δ ρ (n + 1) (affineConstraintAngles (2 * Real.pi * l + a) x) *
          F (affineConstraintAngles (2 * Real.pi * l + a) x) := by
  obtain ⟨l₀, hscalar, hzero⟩ := compactRightCutoff_unique_lift h (a - ∑ i, x i)
  have hFs (l : ℤ) : F (affineConstraintAngles (2 * Real.pi * l + a) x) =
      F (affineConstraintAngles a x) := by rw [affineConstraintAngles_last_period, hF]
  have hprod (l : ℤ) : compactRightProduct b δ ρ (n + 1)
      (affineConstraintAngles (2 * Real.pi * l + a) x) =
        (∏ i : Fin n, (periodicRightCutoff b δ ρ (x i) : ℂ)) *
          (compactRightCutoff b δ ρ ((a - ∑ i, x i) + (l : ℝ) * (2 * Real.pi)) : ℂ) := by
    simp only [compactRightProduct, affineConstraintAngles_eq_snoc, Fin.prod_univ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_last]
    have he : 2 * Real.pi * l + a - ∑ i, x i = (a - ∑ i, x i) + (l : ℝ) * (2 * Real.pi) := by ring
    rw [he]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [compactRightCutoff_eq_periodic h ⟨hx.1 i, hx.2 i⟩]
  have hmain : rightCutoffProduct b δ ρ (n + 1) (affineConstraintAngles a x) * F (affineConstraintAngles a x) =
      compactRightProduct b δ ρ (n + 1) (affineConstraintAngles (2 * Real.pi * l₀ + a) x) *
        F (affineConstraintAngles (2 * Real.pi * l₀ + a) x) := by
    rw [hprod, hscalar, hFs]
    simp only [rightCutoffProduct, affineConstraintAngles_eq_snoc, Fin.prod_univ_castSucc,
      Fin.snoc_castSucc, Fin.snoc_last]
  rw [hmain]
  symm
  apply Finset.sum_eq_single l₀
  · intro l _ hl
    rw [hprod, hzero l hl, Complex.ofReal_zero, mul_zero, zero_mul]
  · intro hl
    have hp : compactRightProduct b δ ρ (n + 1)
        (affineConstraintAngles (2 * Real.pi * l₀ + a) x) = 0 := by
      by_contra hn
      exact hl (compactRightProduct_admissible_lift h hδ hρ a x l₀ hn)
    rw [hp, zero_mul]

end IsingBulk.AnisoF002.Isotropic
