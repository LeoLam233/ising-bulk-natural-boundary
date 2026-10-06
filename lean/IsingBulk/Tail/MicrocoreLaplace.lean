import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! The exact scalar Laplace budget used after the microcore product estimate.
These are scalar integral lemmas, not a substitute for the source contour
change of variables, domination, or Lie-differentiation obligations. -/
namespace IsingBulk.Tail
noncomputable section
open Set MeasureTheory

/-- Integrability is established explicitly before using the improper integral. -/
theorem microcore_inverse_power_integrable (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-(n+2 : ℝ))) (Ioi a⁻¹) := by
  exact integrableOn_Ioi_rpow_of_lt
    (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) (inv_pos.mpr ha)

theorem microcore_constant_integrable (n : ℕ) (a : ℝ) :
    IntervalIntegrable (fun _t : ℝ => a^(n+2)) volume 0 a⁻¹ :=
  intervalIntegrable_const

/-- The large-Laplace-parameter part, in every dimension N=n+2≥2. -/
theorem microcore_inverse_power_integral (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi a⁻¹, t ^ (-(n+2 : ℝ))) = a^(n+1)/(n+1 : ℝ) := by
  rw [integral_Ioi_rpow_of_lt (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith : -(n+2 : ℝ) < -1) (inv_pos.mpr ha)]
  have he : -(n+2 : ℝ)+1 = -(n+1 : ℝ) := by ring
  rw [he, Real.rpow_neg (le_of_lt (inv_pos.mpr ha))]
  rw [show (n : ℝ)+1 = ((n+1 : ℕ) : ℝ) by simp, Real.rpow_natCast]
  simp only [inv_pow, inv_inv, neg_div_neg_eq]

/-- The short-Laplace-parameter part at the reciprocal cutoff. -/
theorem microcore_constant_integral (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ _t : ℝ in (0)..a⁻¹, a^(n+2)) = a^(n+1) := by
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  rw [show n+2=(n+1)+1 by omega, pow_succ]
  field_simp

/-- Exact sum of the two Laplace pieces; no dimension-dependent hidden constant. -/
theorem microcore_laplace_budget (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ _t : ℝ in (0)..a⁻¹, a^(n+2)) +
      (∫ t : ℝ in Ioi a⁻¹, t ^ (-(n+2 : ℝ))) ≤ 2*a^(n+1) := by
  rw [microcore_constant_integral n ha, microcore_inverse_power_integral n ha]
  have hn : (1 : ℝ) ≤ n+1 := by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hp : 0 ≤ a^(n+1) := pow_nonneg ha.le _
  have hd : a^(n+1)/(n+1 : ℝ) ≤ a^(n+1) := div_le_self hp hn
  linarith

theorem microcore_min_eq_short (n : ℕ) {a t : ℝ} (ha : 0 < a)
    (ht : 0 < t) (htcut : t ≤ a⁻¹) :
    (min a t⁻¹)^(n+2) = a^(n+2) := by
  have h : a ≤ t⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_right htcut ha.le
    rw [inv_mul_cancel₀ ha.ne'] at hh
    nlinarith
  rw [min_eq_left h]

theorem microcore_min_eq_long (n : ℕ) {a t : ℝ} (ha : 0 < a)
    (htcut : a⁻¹ < t) :
    (min a t⁻¹)^(n+2) = t^(-(n+2 : ℝ)) := by
  have ht : 0 < t := (inv_pos.mpr ha).trans htcut
  have h : t⁻¹ ≤ a := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_right htcut.le ha.le
    rw [inv_mul_cancel₀ ha.ne'] at hh
    nlinarith
  rw [min_eq_right h]
  rw [show -(n+2 : ℝ) = -((n+2 : ℕ):ℝ) by push_cast; rfl,
    Real.rpow_neg ht.le,Real.rpow_natCast,inv_pow]

theorem microcore_laplace_min_integrable (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (min a t⁻¹)^(n+2)) (Ioi 0) := by
  have he : Ioi (0:ℝ) = Ioc 0 a⁻¹ ∪ Ioi a⁻¹ := by
    ext t
    simp only [mem_Ioi,mem_union,mem_Ioc]
    constructor
    · intro h; by_cases ht : t ≤ a⁻¹
      · exact Or.inl ⟨h,ht⟩
      · exact Or.inr (lt_of_not_ge ht)
    · rintro (h|h)
      · exact h.1
      · exact (inv_pos.mpr ha).trans h
  rw [he,integrableOn_union]
  constructor
  · apply (integrableOn_const (C := a^(n+2)) (μ := volume)
      (s := Ioc (0:ℝ) a⁻¹) (measure_Ioc_lt_top (μ := volume)).ne).congr_fun _ measurableSet_Ioc
    intro t ht
    exact (microcore_min_eq_short n ha ht.1 ht.2).symm
  · apply (microcore_inverse_power_integrable n ha).congr_fun _ measurableSet_Ioi
    intro t ht
    exact (microcore_min_eq_long n ha ht).symm

theorem microcore_laplace_min_bound (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, (min a t⁻¹)^(n+2)) ≤ 2*a^(n+1) := by
  have he : Ioi (0:ℝ) = Ioc 0 a⁻¹ ∪ Ioi a⁻¹ := by
    ext t
    simp only [mem_Ioi,mem_union,mem_Ioc]
    constructor
    · intro h; by_cases ht : t ≤ a⁻¹
      · exact Or.inl ⟨h,ht⟩
      · exact Or.inr (lt_of_not_ge ht)
    · rintro (h|h)
      · exact h.1
      · exact (inv_pos.mpr ha).trans h
  have hi := microcore_laplace_min_integrable n ha
  rw [he,integrableOn_union] at hi
  rw [he,setIntegral_union (by
    apply Set.disjoint_left.mpr
    intro t ht hu
    exact (not_lt_of_ge ht.2) hu) measurableSet_Ioi hi.1 hi.2]
  have hL : (∫ t : ℝ in Ioc 0 a⁻¹, (min a t⁻¹)^(n+2)) =
      ∫ _t : ℝ in 0..a⁻¹, a^(n+2) := by
    rw [intervalIntegral.integral_of_le (inv_nonneg.mpr ha.le)]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact microcore_min_eq_short n ha ht.1 ht.2
  have hR : (∫ t : ℝ in Ioi a⁻¹, (min a t⁻¹)^(n+2)) =
      ∫ t : ℝ in Ioi a⁻¹, t^(-(n+2 : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact microcore_min_eq_long n ha ht
  rw [hL,hR]
  exact microcore_laplace_budget n ha

end
end IsingBulk.Tail
