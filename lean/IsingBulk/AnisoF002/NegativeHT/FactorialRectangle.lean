import IsingBulk.AnisoF002.NegativeHT.ExactFactors

/-!
# Exact factorial-product second differences

The step size is an arbitrary natural d (in F002, d=2p). All identities are
finite sums of exact factors. The final bound has the explicit O_d(1/n)
remainder required for this contribution to the discrete curvature estimate.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open scoped BigOperators

noncomputable section

/-- Telescoping over an arbitrary integer block. -/
theorem block_difference (f : ℕ → ℝ) (n d : ℕ) :
    f (n+d)-f n = ∑ i ∈ Finset.range d, (f (n+i+1)-f (n+i)) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      have heq : n+(d+1) = n+d+1 := by omega
      rw [heq]
      linarith

/-- Logarithm of the exact factorial recursion. -/
theorem log_factorial_step (n : ℕ) :
    Real.log (Nat.factorial (n+1):ℝ) - Real.log (Nat.factorial n:ℝ) =
      Real.log ((n+1:ℕ):ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) (by exact_mod_cast Nat.factorial_ne_zero n)]
  ring

/-- A finite factorial quotient is a block sum of exact logarithms. -/
theorem log_factorial_block (n d : ℕ) :
    Real.log (Nat.factorial (n+d):ℝ) - Real.log (Nat.factorial n:ℝ) =
      ∑ i ∈ Finset.range d, Real.log ((n+i+1:ℕ):ℝ) := by
  rw [block_difference (fun k => Real.log (Nat.factorial k:ℝ)) n d]
  apply Finset.sum_congr rfl
  intro i hi
  exact log_factorial_step (n+i)

/-- Exact one-step logarithmic P_n recursion. -/
theorem log_factorialProduct_step (n : ℕ) :
    Real.log (factorialProduct (n+1)) - Real.log (factorialProduct n) =
      Real.log (Nat.factorial n:ℝ) - (n:ℝ)*Real.log 2 := by
  have hn : (Nat.factorial n:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [factorialProduct_step, Real.log_mul (factorialProduct_pos n).ne'
    (div_ne_zero hn (by positivity)), Real.log_div hn (by positivity), Real.log_pow]
  ring

/-- Exact factorial rectangle, with no differentiated asymptotic notation. -/
theorem log_factorialProduct_rectangle (n d : ℕ) :
    Real.log (factorialProduct (n+2*d)) -
      2*Real.log (factorialProduct (n+d)) + Real.log (factorialProduct n) =
    ∑ i ∈ Finset.range d, ∑ j ∈ Finset.range d,
      (Real.log ((n+i+j+1:ℕ):ℝ) - Real.log 2) := by
  let f : ℕ → ℝ := fun k => Real.log (factorialProduct k)
  have hA := block_difference f (n+d) d
  have hB := block_difference f n d
  have hbase : n+d+d = n+2*d := by omega
  rw [hbase] at hA
  change f (n+2*d) - 2*f (n+d) + f n = _
  calc
    f (n+2*d)-2*f (n+d)+f n =
        (f (n+2*d)-f (n+d)) - (f (n+d)-f n) := by ring
    _ = ∑ i ∈ Finset.range d,
        ((f (n+d+i+1)-f (n+d+i)) - (f (n+i+1)-f (n+i))) := by
          rw [hA, hB, ← Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [f]
      rw [log_factorialProduct_step, log_factorialProduct_step]
      have hb := log_factorial_block (n+i) d
      have hidx : n+d+i = n+i+d := by omega
      rw [hidx]
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      push_cast at hb
      linarith

/-- Elementary exact log increment inequality used to bound each factor. -/
theorem log_increment_bounds {x y : ℝ} (hx : 0<x) (hy : 0≤y) :
    0 ≤ Real.log (x+y)-Real.log x ∧
      Real.log (x+y)-Real.log x ≤ y/x := by
  have hxy : 0<x+y := by linarith
  constructor
  · exact sub_nonneg.mpr (Real.log_le_log hx (by linarith))
  · have h := Real.log_le_sub_one_of_pos (div_pos hxy hx)
    rw [Real.log_div hxy.ne' hx.ne'] at h
    have heq : (x+y)/x-1 = y/x := by field_simp; ring
    rwa [heq] at h

/-- A quantitative remainder for the exact factorial rectangle. No constants
are implicit: the error is between 0 and 2*d^3/n. -/
theorem log_factorialProduct_rectangle_remainder (n d : ℕ) (hn : 0<n) :
    let R := Real.log (factorialProduct (n+2*d)) -
      2*Real.log (factorialProduct (n+d)) + Real.log (factorialProduct n) -
      (d:ℝ)^2 * (Real.log (n:ℝ)-Real.log 2)
    0 ≤ R ∧ R ≤ 2*(d:ℝ)^3/(n:ℝ) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have heq : Real.log (factorialProduct (n+2*d)) -
      2*Real.log (factorialProduct (n+d)) + Real.log (factorialProduct n) -
      (d:ℝ)^2 * (Real.log (n:ℝ)-Real.log 2) =
      ∑ i ∈ Finset.range d, ∑ j ∈ Finset.range d,
        (Real.log ((n+i+j+1:ℕ):ℝ)-Real.log (n:ℝ)) := by
    rw [log_factorialProduct_rectangle]
    simp_rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  dsimp only
  rw [heq]
  have hterm : ∀ i ∈ Finset.range d, ∀ j ∈ Finset.range d,
      0 ≤ Real.log ((n+i+j+1:ℕ):ℝ)-Real.log (n:ℝ) ∧
      Real.log ((n+i+j+1:ℕ):ℝ)-Real.log (n:ℝ) ≤ (2*(d:ℝ))/(n:ℝ) := by
    intro i hi j hj
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hb := log_increment_bounds hn' (show (0:ℝ)≤(i:ℝ)+j+1 by positivity)
    have he : ((n+i+j+1:ℕ):ℝ) = (n:ℝ)+((i:ℝ)+j+1) := by push_cast; ring
    rw [he]
    refine ⟨hb.1, hb.2.trans ?_⟩
    apply div_le_div_of_nonneg_right _ hn'.le
    have : i+j+1 ≤ 2*d := by omega
    exact_mod_cast this
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    exact (hterm i hi j hj).1
  · calc
      _ ≤ ∑ i ∈ Finset.range d, ∑ j ∈ Finset.range d, 2*(d:ℝ)/(n:ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact (hterm i hi j hj).2
      _ = 2*(d:ℝ)^3/(n:ℝ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

end

end IsingBulk.AnisoF002.NegativeHT
