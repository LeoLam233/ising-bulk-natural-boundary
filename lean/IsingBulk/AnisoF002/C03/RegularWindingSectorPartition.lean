import IsingBulk.AnisoF002.C03.RegularWindingSectorGeometry
import IsingBulk.AnisoF002.C03.RegularWindingTorusMeasure

/-!
# Exact partition of the complete inner torus integral into all odd windings

The cutoff is literal and the measure is ordinary Lebesgue measure in the
independent angles.  The finite index set contains every possible sector;
all excluded odd windings have empty support by the proved short-lift bound.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped BigOperators Classical

def AllAnglePeriodic {N : ℕ} (F : (Fin N → ℝ) → ℂ) : Prop :=
  ∀ k : Fin N → ℤ, ∀ q : Fin N → ℝ,
    F (fun i => q i + (k i : ℝ) * (2 * Real.pi)) = F q

def shortCutDensity {N : ℕ} (s : ℝ) (F : (Fin N → ℝ) → ℂ) (q : Fin N → ℝ) : ℂ :=
  if angularShortSquare q ≤ s then F q else 0

def windingCutDensity (n : ℕ) (s : ℝ) (F : (Fin (n + 1) → ℝ) → ℂ)
    (w : ℤ) (x : Fin n → ℝ) : ℂ :=
  if windingSquare n w x ≤ s then F (windingAngles n w x) else 0

def windingSectorIndices (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-(n + 1 : ℤ)) (n + 1)).filter Odd

theorem windingIndex_mem {n : ℕ} (x : Fin n → ℝ) (hx : x ∈ regularAngularBox n) :
    windingIndex x ∈ windingSectorIndices n := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (windingIndex_bound x hx), windingIndex_odd x⟩

theorem allAnglePeriodic_constrained {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℂ}
    (hp : AllAnglePeriodic F) :
    AllAnglePeriodic (fun q : Fin n → ℝ => F (negativeConstrainedAngles q)) := by
  intro k q
  change F (negativeConstrainedAngles (fun i => q i + (k i : ℝ) * (2 * Real.pi))) =
    F (negativeConstrainedAngles q)
  have he : negativeConstrainedAngles (fun i => q i + (k i : ℝ) * (2 * Real.pi)) =
      fun i => negativeConstrainedAngles q i +
        ((Fin.snoc (α := fun _ => ℤ) k (-(∑ j, k j)) i : ℤ) : ℝ) * (2 * Real.pi) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [negativeConstrainedAngles, flatConstrainedAngles, Fin.snoc_last,
        Finset.sum_add_distrib, ← Finset.sum_mul, Int.cast_neg, Int.cast_sum]
      ring
    · simp only [negativeConstrainedAngles, flatConstrainedAngles, Fin.snoc_castSucc]
      ring
  rw [he]
  exact hp _ _

theorem allAnglePeriodic_negative_half_shift {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℂ}
    (hp : AllAnglePeriodic F) (hn : Odd (n + 1)) (q : Fin n → ℝ) :
    F (negativeConstrainedAngles (q + fun _ => Real.pi)) = F (windingAngles n 1 q) := by
  obtain ⟨k, hk⟩ := hn
  have hkr : (n : ℝ) + 1 = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
  have he : negativeConstrainedAngles (q + fun _ => Real.pi) =
      fun i => windingAngles n 1 q i +
        ((Fin.snoc (α := fun _ => ℤ) (fun _ : Fin n => (0 : ℤ)) (-(k + 1 : ℤ)) i : ℤ) : ℝ) * (2 * Real.pi) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [negativeConstrainedAngles, flatConstrainedAngles, Fin.snoc_last,
        Pi.add_apply, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, windingAngles_last, Int.cast_neg, Int.cast_add,
        Int.cast_one, Int.cast_natCast]
      linear_combination -Real.pi * hkr
    · simp only [negativeConstrainedAngles, flatConstrainedAngles, Fin.snoc_castSucc,
        Pi.add_apply, windingAngles_castSucc, Int.cast_zero, zero_mul, add_zero, add_sub_cancel_right]
  rw [he]
  exact hp _ _

theorem allAnglePeriodic_index_reduce {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℂ}
    (hp : AllAnglePeriodic F) (q : Fin n → ℝ) :
    F (windingAngles n 1 q) = F (windingAngles n (windingIndex q) q) := by
  have he : windingAngles n 1 q =
      fun i => windingAngles n (windingIndex q) q i +
        ((Fin.snoc (α := fun _ => ℤ) (fun _ : Fin n => (0 : ℤ)) (windingShortDiv (Real.pi - ∑ j, q j)) i : ℤ) : ℝ) *
          (2 * Real.pi) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [windingAngles_last, windingAngles_index_last, Fin.snoc_last, windingShortAngle_formula]
      simp only [Int.cast_one]
      ring
    · simp only [windingAngles_castSucc, Fin.snoc_castSucc, Int.cast_zero, zero_mul, add_zero]
  rw [he]
  exact hp _ _

theorem windingSector_pointwise {n : ℕ} {s : ℝ} (F : (Fin (n + 1) → ℝ) → ℂ)
    (hp : AllAnglePeriodic (shortCutDensity s F)) (hs : s < Real.pi ^ 2)
    (q : Fin n → ℝ) (hq : q ∈ regularAngularBox n) :
    shortCutDensity s F (windingAngles n 1 q) =
      ∑ w ∈ windingSectorIndices n, windingCutDensity n s F w q := by
  rw [allAnglePeriodic_index_reduce hp q]
  have he : shortCutDensity s F (windingAngles n (windingIndex q) q) =
      windingCutDensity n s F (windingIndex q) q := by
    rw [shortCutDensity, ← windingSquare_eq_shortSquare q hq]
    rfl
  rw [he]
  symm
  apply Finset.sum_eq_single (windingIndex q)
  · intro w hw hne
    unfold windingCutDensity
    apply ite_eq_right
    intro hcut
    have hod := (Finset.mem_filter.mp hw).2
    exact hne (windingIndex_eq_of_sector hod hs hcut).symm
  · intro hnot
    exact (hnot (windingIndex_mem q hq)).elim

theorem windingCutDensity_eq_zero_off_box {n : ℕ} {s : ℝ}
    (F : (Fin (n + 1) → ℝ) → ℂ) (hs : s < Real.pi ^ 2) (w : ℤ)
    (q : Fin n → ℝ) (hq : q ∉ regularAngularBox n) : windingCutDensity n s F w q = 0 := by
  unfold windingCutDensity
  apply ite_eq_right
  intro hcut
  exact hq (windingSquare_support_box hs hcut)

theorem windingCutDensity_eq_zero_outside_indices {n : ℕ} {s : ℝ}
    (F : (Fin (n + 1) → ℝ) → ℂ) (hs : s < Real.pi ^ 2) {w : ℤ}
    (hw : Odd w) (hnot : w ∉ windingSectorIndices n) (q : Fin n → ℝ) :
    windingCutDensity n s F w q = 0 := by
  unfold windingCutDensity
  apply ite_eq_right
  intro hcut
  have hq := windingSquare_support_box hs hcut
  have he := windingIndex_eq_of_sector hw hs hcut
  exact hnot (he ▸ windingIndex_mem q hq)

theorem windingSector_integral {n : ℕ} {s : ℝ} (F : (Fin (n + 1) → ℝ) → ℂ)
    (hp : AllAnglePeriodic (shortCutDensity s F)) (hn : Odd (n + 1)) (hs : s < Real.pi ^ 2)
    (hint : ∀ w ∈ windingSectorIndices n, Integrable (windingCutDensity n s F w)) :
    (∫ q in regularAngularBox n, shortCutDensity s F (negativeConstrainedAngles q)) =
      ∑ w ∈ windingSectorIndices n, ∫ q, windingCutDensity n s F w q := by
  have hshift := regularAngularBox_integral_shift_measurable n
    (fun q => shortCutDensity s F (negativeConstrainedAngles q))
    (allAnglePeriodic_constrained hp) (fun _ => Real.pi)
  rw [← hshift]
  simp_rw [allAnglePeriodic_negative_half_shift hp hn]
  have hpoint : (∫ q in regularAngularBox n, shortCutDensity s F (windingAngles n 1 q)) =
      ∫ q in regularAngularBox n, ∑ w ∈ windingSectorIndices n, windingCutDensity n s F w q := by
    exact setIntegral_congr_fun measurableSet_Icc (windingSector_pointwise F hp hs)
  rw [hpoint, integral_finsetSum _ (fun w hw => (hint w hw).integrableOn)]
  apply Finset.sum_congr rfl
  intro w _
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (windingCutDensity_eq_zero_off_box F hs w)

end
end IsingBulk.AnisoF002.NegativeHT
