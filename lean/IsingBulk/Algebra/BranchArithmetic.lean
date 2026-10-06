import IsingBulk.Algebra.PrimeFamily
import IsingBulk.Algebra.Resultant
import Mathlib.FieldTheory.NormalizedTrace
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Arithmetic of the exact branch in rc4, thm:prime and lem:resultant. -/

namespace IsingBulk.PrimeFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial IntermediateField
open scoped IntermediateField

/-- The relative algebraic closure uses the actual embedding into the complex numbers. -/
noncomputable abbrev AlgebraicComplex := algebraicClosure ℚ ℂ

theorem normalizedTrace_primitive_root {L : Type*} [Field L] [Algebra ℚ L]
    [Algebra.IsIntegral ℚ L] {p : ℕ} (hp : p.Prime)
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    Algebra.normalizedTrace ℚ L ζ = -((p - 1 : ℕ) : ℚ)⁻¹ := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  rw [Algebra.normalizedTrace_minpoly,
    ← hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hp.pos)]
  have hc : (cyclotomic p ℚ).nextCoeff = 1 := by
    rw [nextCoeff, ite_eq_right (by rw [natDegree_cyclotomic]; exact (Nat.totient_pos.mpr hp.pos).ne'), natDegree_cyclotomic,
      Nat.totient_prime hp, cyclotomic_prime]
    simp [coeff_X_pow, Finset.mem_range, show p-1-1 < p by have := hp.two_le; omega]
  simp [hc, natDegree_cyclotomic, Nat.totient_prime hp]

/-- Each root of unity has normalized trace at least -1. This is the
average of the real parts of its complex conjugates. -/
theorem normalizedTrace_root_unity_lower (z : AlgebraicComplex) {N : ℕ}
    (hN : 0 < N) (hz : z ^ N = 1) :
    (-1 : ℚ) ≤ Algebra.normalizedTrace ℚ AlgebraicComplex z := by
  classical
  let K := ℚ⟮z⟯
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
  let x : K := AdjoinSimple.gen ℚ z
  have hx : x ^ N = 1 := by
    apply Subtype.ext
    exact hz
  have he (σ : K →ₐ[ℚ] ℂ) : -1 ≤ (σ x).re := by
    have hn : ‖σ x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one
      (by simpa using congrArg σ hx) hN.ne'
    have hab := Complex.abs_re_le_norm (σ x)
    rw [hn] at hab
    exact (abs_le.mp hab).1
  have ht := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := x)
  have hreal : (Algebra.trace ℚ K x : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ x).re := by
    simpa using congrArg Complex.re ht
  have hsum : -(Module.finrank ℚ K : ℝ) ≤ (Algebra.trace ℚ K x : ℝ) := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun σ _ => he σ)
    rw [hreal]
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_neg, mul_one, AlgHom.card] using hs
  have hd : (0 : ℝ) < Module.finrank ℚ K := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  rw [Algebra.normalizedTrace_def]
  change (-1 : ℚ) ≤ (Module.finrank ℚ K : ℚ)⁻¹ * Algebra.trace ℚ K x
  have hq : -(Module.finrank ℚ K : ℚ) ≤ Algebra.trace ℚ K x := by exact_mod_cast hsum
  have hdq : (0 : ℚ) < Module.finrank ℚ K := by exact_mod_cast hd
  rw [← div_eq_inv_mul, le_div_iff₀ hdq]
  simpa using hq

/-- The trace obstruction is proved in the embedded algebraic closure; no
choice of a different complex root is made. -/
theorem branch_trace_obstruction {p : ℕ} (hp : p.Prime)
    {r s z : AlgebraicComplex} (hr : IsPrimitiveRoot r p) (hs : IsPrimitiveRoot s p)
    (hrel : z + z⁻¹ = r + r⁻¹ + s + s⁻¹ - 2) : ¬ IsOfFinOrder z := by
  intro hz
  obtain ⟨N, hN, hzN⟩ := isOfFinOrder_iff_pow_eq_one.mp hz
  have hlow := normalizedTrace_root_unity_lower z hN hzN
  have hinv := normalizedTrace_root_unity_lower z⁻¹ hN (by simp [inv_pow, hzN])
  have htwo : Algebra.normalizedTrace ℚ AlgebraicComplex 2 = 2 := by
    simpa using Algebra.normalizedTrace_algebraMap_apply ℚ ℚ AlgebraicComplex 2
  have ht := congrArg (Algebra.normalizedTrace ℚ AlgebraicComplex) hrel
  rw [map_add, map_sub, map_add, map_add, map_add,
    normalizedTrace_primitive_root hp hr, normalizedTrace_primitive_root hp hr.inv,
    normalizedTrace_primitive_root hp hs, normalizedTrace_primitive_root hp hs.inv, htwo] at ht
  have hd : (0 : ℚ) < ((p - 1 : ℕ) : ℚ)⁻¹ := by
    apply inv_pos.mpr
    exact_mod_cast (show 0 < p - 1 by have := hp.two_le; omega)
  linarith

/-- Algebraicity of a nonzero solution of x + x⁻¹ = w, for algebraic w.
This uses the monic quadratic over the algebraic closure, followed by transitivity. -/
theorem algebraic_of_add_inv {z w : ℂ} (hz : z ≠ 0) (hw : IsAlgebraic ℚ w)
    (hrel : z + z⁻¹ = w) : IsAlgebraic ℚ z := by
  let w' : AlgebraicComplex := ⟨w, mem_algebraicClosure_iff.mpr hw⟩
  have hi : IsIntegral AlgebraicComplex z := by
    refine ⟨X ^ 2 - C w' * X + 1, ?_, ?_⟩
    · monicity <;> norm_num
    · simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_one]
      change z ^ 2 - w * z + 1 = 0
      rw [← hrel]
      field_simp [hz]
      ring
  exact (isIntegral_trans (R := ℚ) z hi).isAlgebraic

theorem primitive_sum_not_nonneg_rational {L : Type*} [Field L] [Algebra ℚ L]
    [Algebra.IsIntegral ℚ L] {p : ℕ} (hp : p.Prime) {r s : L}
    (hr : IsPrimitiveRoot r p) (hs : IsPrimitiveRoot s p)
    {q : ℚ} (hq : 0 ≤ q) : r + r⁻¹ + s + s⁻¹ ≠ algebraMap ℚ L q := by
  intro h
  have ht := congrArg (Algebra.normalizedTrace ℚ L) h
  rw [map_add, map_add, map_add, normalizedTrace_primitive_root hp hr,
    normalizedTrace_primitive_root hp hr.inv, normalizedTrace_primitive_root hp hs,
    normalizedTrace_primitive_root hp hs.inv,
    Algebra.normalizedTrace_algebraMap_apply ℚ ℚ L, Algebra.normalizedTrace_self_apply] at ht
  have hd : (0 : ℚ) < ((p - 1 : ℕ) : ℚ)⁻¹ := by
    apply inv_pos.mpr
    exact_mod_cast (show 0 < p - 1 by have := hp.two_le; omega)
  linarith

end IsingBulk.PrimeFamily
