import IsingBulk.AnisoF002.C03.RegularWindingNumeratorBound
import IsingBulk.AnisoF002.C03.NegativeCoefficientDisks
import IsingBulk.AnisoF002.C03.NegativeInnerAngularCut
import IsingBulk.AnisoF002.C03.NegativeAngularCoordinates
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# The actual signed short-lift winding sectors

All odd windings are retained.  The final angle is the signed representative
of pi minus the sum of the independent angles.  The quadratic cutoff is
exactly the sum of the squared short lifts, with no replacement by a bound.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set IsingBulk.AnisoF002.RegularTail.C03 IsingBulk.AnisoF002.Isotropic
open scoped BigOperators

def windingShortAngle (x : ℝ) : ℝ := toIocMod Real.two_pi_pos (-Real.pi) x

def windingShortDiv (x : ℝ) : ℤ := toIocDiv Real.two_pi_pos (-Real.pi) x

theorem windingShortAngle_formula (x : ℝ) :
    windingShortAngle x = x - (windingShortDiv x : ℝ) * (2 * Real.pi) := by
  exact (self_sub_toIocDiv_mul Real.two_pi_pos (-Real.pi) x).symm

theorem windingShortAngle_mem (x : ℝ) : windingShortAngle x ∈ Ioc (-Real.pi) Real.pi := by
  simpa only [windingShortAngle, show -Real.pi + 2 * Real.pi = Real.pi by ring] using
    toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) x

theorem windingShortAngle_abs_le (x : ℝ) : |windingShortAngle x| ≤ Real.pi :=
  abs_le.mpr ⟨(windingShortAngle_mem x).1.le, (windingShortAngle_mem x).2⟩

theorem windingShortAngle_cos (x : ℝ) : Real.cos (windingShortAngle x) = Real.cos x := by
  rw [windingShortAngle_formula]
  exact Real.cos_sub_int_mul_two_pi x _

theorem windingShortAngle_eq_self {x : ℝ} (hx : x ∈ Ioc (-Real.pi) Real.pi) :
    windingShortAngle x = x := by
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using hx

theorem unsignedShortAngle_eq_abs_of_abs_le {x : ℝ} (hx : |x| ≤ Real.pi) :
    unsignedShortAngle x = |x| := by
  rw [unsignedShortAngle, ← Real.cos_abs x]
  exact Real.arccos_cos (abs_nonneg x) hx

theorem unsignedShortAngle_sq_of_abs_le {x : ℝ} (hx : |x| ≤ Real.pi) :
    unsignedShortAngle x ^ 2 = x ^ 2 := by
  rw [unsignedShortAngle_eq_abs_of_abs_le hx, sq_abs]

theorem unsignedShortAngle_eq_abs_short (x : ℝ) :
    unsignedShortAngle x = |windingShortAngle x| := by
  rw [unsignedShortAngle, ← windingShortAngle_cos x]
  exact unsignedShortAngle_eq_abs_of_abs_le (windingShortAngle_abs_le x)

def windingAngles (n : ℕ) (w : ℤ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc x ((w : ℝ) * Real.pi - ∑ i, x i)

def windingSquare (n : ℕ) (w : ℤ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, windingAngles n w x i ^ 2

def windingIndex {n : ℕ} (x : Fin n → ℝ) : ℤ :=
  1 - 2 * windingShortDiv (Real.pi - ∑ i, x i)

@[simp] theorem windingAngles_castSucc (n : ℕ) (w : ℤ) (x : Fin n → ℝ) (i : Fin n) :
    windingAngles n w x i.castSucc = x i := by simp [windingAngles]

@[simp] theorem windingAngles_last (n : ℕ) (w : ℤ) (x : Fin n → ℝ) :
    windingAngles n w x (Fin.last n) = (w : ℝ) * Real.pi - ∑ i, x i := by
  simp [windingAngles]

theorem windingAngles_sum (n : ℕ) (w : ℤ) (x : Fin n → ℝ) :
    ∑ i, windingAngles n w x i = (w : ℝ) * Real.pi := by
  simp [Fin.sum_univ_castSucc]

theorem windingIndex_odd {n : ℕ} (x : Fin n → ℝ) : Odd (windingIndex x) := by
  refine ⟨-windingShortDiv (Real.pi - ∑ i, x i), ?_⟩
  unfold windingIndex
  ring

theorem windingAngles_index_last {n : ℕ} (x : Fin n → ℝ) :
    windingAngles n (windingIndex x) x (Fin.last n) =
      windingShortAngle (Real.pi - ∑ i, x i) := by
  rw [windingAngles_last, windingShortAngle_formula]
  simp only [windingIndex, Int.cast_sub, Int.cast_one, Int.cast_mul, Int.cast_ofNat]
  ring

theorem windingAngles_index_abs_le {n : ℕ} (x : Fin n → ℝ) (hx : x ∈ regularAngularBox n)
    (i : Fin (n + 1)) : |windingAngles n (windingIndex x) x i| ≤ Real.pi := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [windingAngles_index_last]
    exact windingShortAngle_abs_le _
  · rw [windingAngles_castSucc]
    exact abs_le.mpr ⟨hx.1 j, hx.2 j⟩

theorem windingIndex_bound {n : ℕ} (x : Fin n → ℝ) (hx : x ∈ regularAngularBox n) :
    -(n + 1 : ℤ) ≤ windingIndex x ∧ windingIndex x ≤ (n + 1 : ℤ) := by
  have hsum : |(windingIndex x : ℝ) * Real.pi| ≤ (n + 1 : ℕ) * Real.pi := by
    rw [← windingAngles_sum n (windingIndex x) x]
    calc
      _ ≤ ∑ i, |windingAngles n (windingIndex x) x i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (n + 1), Real.pi := Finset.sum_le_sum (fun i _ => windingAngles_index_abs_le x hx i)
      _ = _ := by simp
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsum
  have hw : |(windingIndex x : ℝ)| ≤ ((n + 1 : ℕ) : ℝ) := by nlinarith [Real.pi_pos]
  have hh := abs_le.mp hw
  constructor
  · exact_mod_cast hh.1
  · exact_mod_cast hh.2

theorem windingSquare_eq_shortSquare {n : ℕ} (x : Fin n → ℝ) (hx : x ∈ regularAngularBox n) :
    windingSquare n (windingIndex x) x = angularShortSquare (windingAngles n (windingIndex x) x) := by
  apply Finset.sum_congr rfl
  intro i _
  exact (unsignedShortAngle_sq_of_abs_le (windingAngles_index_abs_le x hx i)).symm

theorem windingSquare_coordinate_bound {n : ℕ} {w : ℤ} {x : Fin n → ℝ} {s : ℝ}
    (hs : s < Real.pi ^ 2) (hx : windingSquare n w x ≤ s) (i : Fin (n + 1)) :
    |windingAngles n w x i| < Real.pi := by
  have hi : windingAngles n w x i ^ 2 ≤ windingSquare n w x :=
    Finset.single_le_sum (fun j _ => sq_nonneg (windingAngles n w x j)) (Finset.mem_univ i)
  have hsq : |windingAngles n w x i| ^ 2 < Real.pi ^ 2 := by rw [sq_abs]; exact hi.trans_lt (hx.trans_lt hs)
  nlinarith [abs_nonneg (windingAngles n w x i), Real.pi_pos]

theorem windingSquare_support_box {n : ℕ} {w : ℤ} {x : Fin n → ℝ} {s : ℝ}
    (hs : s < Real.pi ^ 2) (hx : windingSquare n w x ≤ s) : x ∈ regularAngularBox n := by
  constructor <;> intro i
  · have h := (abs_lt.mp (windingSquare_coordinate_bound hs hx i.castSucc)).1
    simpa using h.le
  · have h := (abs_lt.mp (windingSquare_coordinate_bound hs hx i.castSucc)).2
    simpa using h.le

theorem windingIndex_eq_of_sector {n : ℕ} {w : ℤ} {x : Fin n → ℝ} {s : ℝ}
    (hw : Odd w) (hs : s < Real.pi ^ 2) (hx : windingSquare n w x ≤ s) : windingIndex x = w := by
  obtain ⟨k, hk⟩ := hw
  have hc := windingSquare_coordinate_bound hs hx (Fin.last n)
  have hl : windingShortAngle (Real.pi - ∑ i, x i) = windingAngles n w x (Fin.last n) := by
    apply (toIocMod_eq_iff Real.two_pi_pos).mpr
    constructor
    · have ha := abs_lt.mp hc
      simpa only [Set.mem_Ioc, show -Real.pi + 2 * Real.pi = Real.pi by ring] using
        And.intro ha.1 ha.2.le
    · refine ⟨-k, ?_⟩
      rw [windingAngles_last, hk]
      simp only [Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_ofNat, zsmul_eq_mul, Int.cast_neg]
      ring
  have he := (windingAngles_index_last x).trans hl
  rw [windingAngles_last, windingAngles_last] at he
  have hcast : (windingIndex x : ℝ) = (w : ℝ) := by nlinarith [Real.pi_pos]
  exact_mod_cast hcast

theorem windingSquare_lower (n : ℕ) (w : ℤ) (x : Fin n → ℝ) :
    (w : ℝ) ^ 2 * Real.pi ^ 2 / (n + 1 : ℕ) ≤ windingSquare n w x := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin (n + 1) => windingAngles n w x i) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, windingAngles_sum] at hc
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))]
  simpa only [mul_pow, mul_comm, windingSquare] using hc

end
end IsingBulk.AnisoF002.NegativeHT
