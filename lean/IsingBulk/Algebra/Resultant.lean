import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic

/-! Exponential separation, lem:resultant. Uniformity is ∃ A > 0, ∀ N ≥ 1.
The polynomial and non-root-of-unity hypotheses are explicit. -/

namespace IsingBulk
namespace Separation
open Polynomial

theorem norm_pow_sub_one_le (z : ℂ) {N : ℕ} (hN : N ≠ 0) :
    ‖z^N-1‖ ≤ (‖z‖+1)^N := by
  calc
    ‖z^N-1‖ ≤ ‖z^N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = ‖z‖^N + 1^N := by simp
    _ ≤ (‖z‖+1)^N := pow_add_pow_le (norm_nonneg _) zero_le_one hN

theorem norm_prod_pow_sub_one_le (s : Multiset ℂ) {N : ℕ} (hN : N ≠ 0) :
    ‖(s.map (fun z => z^N-1)).prod‖ ≤ ((s.map (fun z => ‖z‖+1)).prod)^N := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, mul_pow]
    exact mul_le_mul (norm_pow_sub_one_le a hN) ih (norm_nonneg _) (by positivity)

theorem one_le_root_bound (s : Multiset ℂ) :
    1 ≤ (s.map (fun z => ‖z‖+1)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact one_le_mul_of_one_le_of_one_le (by linarith [norm_nonneg a]) ih

/-- Absorb a fixed exponential product bound with one constant chosen before N. -/
theorem exponential_of_geometric {u : ℕ → ℝ} {B : ℝ} (hB : 1 < B)
    (h : ∀ N : ℕ, 1 ≤ N → 1 ≤ u N * B^N) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 1 ≤ N → Real.exp (-A * N) ≤ u N := by
  refine ⟨Real.log B, Real.log_pos hB, ?_⟩
  intro N hN
  have hBp : 0 < B := lt_trans zero_lt_one hB
  have he : Real.exp (-Real.log B * (N : ℝ)) = (B^N)⁻¹ := by
    rw [neg_mul, Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hBp]
  rw [he]
  rw [← one_div]
  exact (div_le_iff₀ (pow_pos hBp N)).mpr (h N hN)

/-- A nonzero integer polynomial resultant has complex norm at least one. -/
theorem one_le_norm_intCast {r : ℤ} (hr : r ≠ 0) : 1 ≤ ‖(r : ℂ)‖ := by
  rw [Complex.norm_intCast, ← Int.cast_abs]
  exact_mod_cast (Int.one_le_abs hr)

theorem resultant_nonzero (P : ℤ[X]) {ξ : ℂ}
    (hirr : Irreducible (P.map (algebraMap ℤ ℚ)))
    (hroot : aeval ξ P = 0) {N : ℕ} (hξ : ξ^N ≠ 1) :
    P.resultant (X^N-1) ≠ 0 := by
  have hc : IsCoprime (P.map (algebraMap ℤ ℚ)) (X^N-1) := by
    apply hirr.coprime_iff_not_dvd.mpr
    intro hd
    have hz : aeval ξ (P.map (algebraMap ℤ ℚ)) = 0 := by
      simpa only [aeval_map_algebraMap] using hroot
    have h := aeval_eq_zero_of_dvd_aeval_eq_zero hd hz
    apply hξ
    simpa using (sub_eq_zero.mp (by simpa using h : ξ^N-1=0))
  have hd : (X^N-1 : ℤ[X]).natDegree = N := by
    simpa using (natDegree_X_pow_sub_C (R := ℤ) (n := N) (r := 1))
  have hdq : (X^N-1 : ℚ[X]).natDegree = N := by
    simpa using (natDegree_X_pow_sub_C (R := ℚ) (n := N) (r := 1))
  intro hz
  apply resultant_ne_zero _ _ hc
  have hm := congrArg (algebraMap ℤ ℚ) hz
  rw [← resultant_map_map] at hm
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one] at hm
  have hdp := natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective ℤ ℚ) P
  simpa only [map_sub, map_pow, map_X, map_one, hdp, hd, hdq, map_zero] using hm

theorem exponential_of_integer_polynomial (P : ℤ[X]) (hP : P ≠ 0) {ξ : ℂ}
    (hroot : aeval ξ P = 0)
    (hres : ∀ N : ℕ, 1 ≤ N → P.resultant (X^N-1) ≠ 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 1 ≤ N → Real.exp (-A * N) ≤ ‖1-ξ^N‖ := by
  classical
  let f : ℂ[X] := P.map (algebraMap ℤ ℂ)
  have hf : f ≠ 0 := (Polynomial.map_ne_zero_iff
    (FaithfulSMul.algebraMap_injective ℤ ℂ)).mpr hP
  have hx : ξ ∈ f.roots := (mem_roots hf).mpr (by
    change (P.map (algebraMap ℤ ℂ)).eval ξ = 0
    rw [eval_map]
    exact hroot)
  let s := f.roots.erase ξ
  have hs : f.roots = ξ ::ₘ s := (Multiset.cons_erase hx).symm
  let C : ℝ := (s.map (fun z => ‖z‖+1)).prod
  let B : ℝ := 2 * (max 1 ‖f.leadingCoeff‖) * C
  have hC : 1 ≤ C := one_le_root_bound s
  have hB : 1 < B := by dsimp [B]; nlinarith [le_max_left 1 ‖f.leadingCoeff‖]
  apply exponential_of_geometric hB
  intro N hN
  have hn : N ≠ 0 := by omega
  have hd : (X^N-1 : ℤ[X]).natDegree = N := by
    simpa using (natDegree_X_pow_sub_C (R := ℤ) (n := N) (r := 1))
  have heq : ((P.resultant (X^N-1) : ℤ) : ℂ) =
      f.leadingCoeff^N * (f.roots.map (fun z => z^N-1)).prod := by
    have he := resultant_eq_prod_eval f (X^N-1) N (by
      simpa using (natDegree_X_pow_sub_C (R := ℂ) (n := N) (r := 1)).le)
      (IsAlgClosed.splits f)
    have hdp : f.natDegree = P.natDegree :=
      natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective ℤ ℂ) P
    have hm : (X^N-1 : ℂ[X]) = (X^N-1 : ℤ[X]).map (algebraMap ℤ ℂ) := by simp
    rw [hdp, hm] at he
    change (P.map (algebraMap ℤ ℂ)).resultant _ _ _ = _ at he
    rw [resultant_map_map] at he
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one, eval_sub, eval_pow, eval_X, eval_one] at he
    simpa only [hd, algebraMap_int_eq, Int.coe_castRingHom] using he
  have hb : ‖f.leadingCoeff‖ * C ≤ B := by
    dsimp [B]
    nlinarith [le_max_right 1 ‖f.leadingCoeff‖, le_max_left 1 ‖f.leadingCoeff‖, norm_nonneg f.leadingCoeff]
  calc
    1 ≤ ‖((P.resultant (X^N-1) : ℤ) : ℂ)‖ := one_le_norm_intCast (hres N hN)
    _ = ‖f.leadingCoeff‖^N * (‖ξ^N-1‖ * ‖(s.map (fun z => z^N-1)).prod‖) := by
      rw [heq, hs]; simp
    _ ≤ ‖f.leadingCoeff‖^N * (‖ξ^N-1‖ * C^N) := by
      gcongr
      exact norm_prod_pow_sub_one_le s hn
    _ = ‖1-ξ^N‖ * (‖f.leadingCoeff‖ * C)^N := by
      rw [norm_sub_rev (ξ^N)]; simp only [mul_pow]; ring
    _ ≤ ‖1-ξ^N‖ * B^N := by gcongr

/-- The general algebraic leaf: the same A works for every positive N.
Algebraicity and non-root-of-unity are precisely the facts about the selected
point supplied by thm:prime in the manuscript. -/
theorem exponential_separation {ξ : ℂ} (halg : IsAlgebraic ℚ ξ)
    (hξ : ∀ N : ℕ, 1 ≤ N → ξ^N ≠ 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 1 ≤ N → Real.exp (-A * N) ≤ ‖1-ξ^N‖ := by
  let q := minpoly ℚ ξ
  let P := IsLocalization.integerNormalization (nonZeroDivisors ℤ) q
  obtain ⟨b, hb, hmap⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) q
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
  have heq : b • q = Polynomial.C (b : ℚ) * q := by
    ext i
    simp
  have hirr : Irreducible (P.map (algebraMap ℤ ℚ)) := by
    rw [hmap, heq, irreducible_isUnit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hbq))]
    exact minpoly.irreducible halg.isIntegral
  have hP : P ≠ 0 := by
    intro hz
    apply hirr.ne_zero
    simp [hz]
  have hroot : aeval ξ P = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) q (minpoly.aeval ℚ ξ)
  exact exponential_of_integer_polynomial P hP hroot (fun N hN =>
    resultant_nonzero P hirr hroot (hξ N hN))

theorem exponential_separation_of_not_isOfFinOrder {ξ : ℂ}
    (halg : IsAlgebraic ℚ ξ) (hξ : ¬ IsOfFinOrder ξ) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 1 ≤ N → Real.exp (-A * N) ≤ ‖1-ξ^N‖ := by
  apply exponential_separation halg
  intro N hN heq
  exact hξ (isOfFinOrder_iff_pow_eq_one.mpr ⟨N, hN, heq⟩)

end Separation
end IsingBulk
