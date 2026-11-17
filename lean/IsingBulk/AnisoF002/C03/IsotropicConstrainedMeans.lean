import IsingBulk.AnisoF002.C03.IsotropicCompleteShellCoarea
import Mathlib.Data.Int.Interval

/-!
# All constrained means have only a linear particle-count cost

The exact integer lifts of either physical sign are bounded using the
full right rectangle. No winding is omitted. On the common radius at
most N integer lifts can meet the rectangle.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory

theorem int_interval_card_le_of_real_width (a b : ℝ) (N : ℕ) (hwidth : b - a < N) :
    (Finset.Icc (Int.ceil a) (Int.floor b)).card ≤ N := by
  have hh : ((Int.floor b - Int.ceil a : ℤ) : ℝ) < N := by
    push_cast
    linarith only [Int.floor_le b, Int.le_ceil a, hwidth]
  have hi : Int.floor b - Int.ceil a < (N : ℤ) := by exact_mod_cast hh
  have hj : Int.floor b + 1 - Int.ceil a ≤ (N : ℤ) := by omega
  rw [Int.card_Icc]
  exact (Int.toNat_le_toNat hj).trans_eq (by simp)

def admissibleRightLifts (N : ℕ) (b δ a : ℝ) : Finset ℤ :=
  Finset.Icc (Int.ceil (((N : ℝ) * (-b - δ) - a) / (2 * Real.pi)))
    (Int.floor (((N : ℝ) * δ - a) / (2 * Real.pi)))

theorem admissibleRightLifts_mem_iff (N : ℕ) (b δ a : ℝ) (l : ℤ) :
    l ∈ admissibleRightLifts N b δ a ↔
      (N : ℝ) * (-b - δ) ≤ 2 * Real.pi * l + a ∧ 2 * Real.pi * l + a ≤ (N : ℝ) * δ := by
  have hp : 0 < 2 * Real.pi := by positivity
  rw [admissibleRightLifts, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  rw [div_le_iff₀ hp, le_div_iff₀ hp]
  constructor <;> rintro ⟨hlo, hup⟩ <;> constructor <;> linarith only [hlo, hup]

theorem admissibleRightLifts_card_le (N : ℕ) (hN : 0 < N) (b δ a : ℝ)
    (hb : b < Real.pi) (hδ : δ ≤ 1) : (admissibleRightLifts N b δ a).card ≤ N := by
  apply int_interval_card_le_of_real_width
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hp : 0 < 2 * Real.pi := by positivity
  have hwidth : b + 2 * δ < 2 * Real.pi := by linarith only [hb, hδ, Real.two_le_pi]
  have hm := mul_lt_mul_of_pos_left hwidth hNp
  have he : (((N : ℝ) * δ - a) / (2 * Real.pi)) -
      (((N : ℝ) * (-b - δ) - a) / (2 * Real.pi)) =
      (N : ℝ) * (b + 2 * δ) / (2 * Real.pi) := by ring
  rw [he]
  exact (div_lt_iff₀ hp).mpr hm

def constrainedRightMean (N : ℕ) (b a : ℝ) (l : ℤ) : ℝ :=
  b + (2 * Real.pi * l + a) / N

theorem actual_shell_mean_lift_mem (d : ℕ) (b δ r a : ℝ) (l : ℤ)
    (hcell : (actualCenteredShell d (constrainedRightMean (d + 1) b a l - b) b δ r).Nonempty) :
    l ∈ admissibleRightLifts (d + 1) b δ a := by
  obtain ⟨x, hx⟩ := hcell
  have hN : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsum : (∑ k, centeredConstraintAngles (constrainedRightMean (d + 1) b a l - b) x k) =
      2 * Real.pi * l + a := by
    rw [centeredConstraintAngles_sum]
    simp only [constrainedRightMean, add_sub_cancel_left]
    push_cast at hN ⊢
    field_simp
  have hlo := Finset.sum_le_sum (fun (k : Fin (d + 1)) (_ : k ∈ Finset.univ) => (hx.1 k).1)
  have hup := Finset.sum_le_sum (fun (k : Fin (d + 1)) (_ : k ∈ Finset.univ) => (hx.1 k).2)
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlo hup
  exact (admissibleRightLifts_mem_iff (d + 1) b δ a l).mpr ⟨hlo, hup⟩

theorem actual_shell_empty_off_admissible_lifts (d : ℕ) (b δ r a : ℝ) (l : ℤ)
    (hl : l ∉ admissibleRightLifts (d + 1) b δ a) :
    actualCenteredShell d (constrainedRightMean (d + 1) b a l - b) b δ r = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  exact fun h => hl (actual_shell_mean_lift_mem d b δ r a l h)

end IsingBulk.AnisoF002.Isotropic
