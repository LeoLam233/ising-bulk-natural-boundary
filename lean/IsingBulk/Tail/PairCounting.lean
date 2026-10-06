import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-! The numerical, collision-safe counting part of manuscript Lemma 7.2.
This module does not assume that the geometric pair estimates hold: it states
explicitly the scalar inequalities needed to combine them. In particular,
removed factors never occur in a denominator. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

/-- Three groups have quadratically many within-group pairs. -/
theorem three_group_same_count (a b c : ℝ) :
    (a+b+c)^2/6-(a+b+c)/2 ≤
      (a*(a-1)+b*(b-1)+c*(c-1))/2 := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]

/-- The cross-group count is at most n²/3, with no balance assumption. -/
theorem three_group_cross_count (a b c : ℝ) :
    a*b+a*c+b*c ≤ (a+b+c)^2/3 := by
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c)]

/-- Deleting at most j edges is handled by subtraction of cardinalities,
not division by a product that can be zero. -/
theorem remaining_card_lower {α : Type*} [DecidableEq α]
    (s E : Finset α) (j : ℕ) (hE : E.card ≤ j) :
    (s.card : ℝ) - j ≤ ((s \ E).card : ℝ) := by
  have h := Finset.card_sdiff_add_card_inter s E
  have hi : (s ∩ E).card ≤ E.card := Finset.card_le_card Finset.inter_subset_right
  have hh : s.card ≤ (s \ E).card + j := by omega
  exact_mod_cast (show (s.card : ℤ) - j ≤ (s \ E).card by omega)

/-- A direct bound for every surviving factor. Zero factors are allowed. -/
theorem remaining_product_le {α : Type*} [DecidableEq α]
    (s E : Finset α) (f b : α → ℝ)
    (hf : ∀ e ∈ s, 0 ≤ f e)
    (hb : ∀ e ∈ s, f e ≤ b e) :
    (∏ e ∈ s \ E, f e) ≤ ∏ e ∈ s \ E, b e := by
  exact Finset.prod_le_prod₀
    (fun e he => hf e (Finset.mem_sdiff.mp he).1)
    (fun e he => hb e (Finset.mem_sdiff.mp he).1)

/-- The cross slack consumes only half the quadratic contraction.
Here l=log q'<0 and h=log(1+η)≥0. Negative same-count lower bounds
remain permissible. -/
theorem remaining_log_bound (n j same cross l h : ℝ)
    (hl : l < 0) (hh : 0 ≤ h) (hslack : h ≤ -l/4)
    (hsame : n^2/6-n/2-j ≤ same)
    (hcross : cross ≤ n^2/3) :
    same*l+cross*h ≤ (n^2/12-n/2-j)*l := by
  have h₁ := mul_le_mul_of_nonpos_right hsame (le_of_lt hl)
  have h₂ := mul_le_mul_of_nonneg_right hcross hh
  have h₃ := mul_le_mul_of_nonneg_left hslack (show 0 ≤ n^2/3 by positivity)
  nlinarith

/-- The named Stokes index leaves N-1 lower variables. The linear
correction is exactly -2N/3, rather than the K value -N/2. -/
theorem stokes_exponent_identity (N j : ℝ) :
    (N-1)^2/12-(N-1)/2-j = N^2/12-2*N/3+7/12-j := by ring

/-- Direct finite-product estimate after deleting any set of factors. The
surviving factors may vanish, and no positivity of them is required. -/
theorem product_exp_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (f b : α → ℝ)
    (hf : ∀ e ∈ s, 0 ≤ f e)
    (hb : ∀ e ∈ s, f e ≤ Real.exp (b e)) :
    (∏ e ∈ s, f e) ≤ Real.exp (∑ e ∈ s, b e) := by
  calc
    _ ≤ ∏ e ∈ s, Real.exp (b e) := Finset.prod_le_prod₀ hf hb
    _ = _ := (Real.exp_sum s b).symm

/-- The lower-pair estimate, including deleted edges, with actual exponential
quadratic suppression. Geometric group bounds must be established separately. -/
theorem surviving_pair_suppression {α : Type*} [DecidableEq α]
    (s : Finset α) (same : α → Prop) [DecidablePred same]
    (f : α → ℝ) (n j l h : ℝ)
    (hl : l < 0) (hh : 0 ≤ h) (hslack : h ≤ -l/4)
    (hcount : n^2/6-n/2-j ≤ ((s.filter same).card : ℝ))
    (hcross : ((s.filter (fun e => ¬ same e)).card : ℝ) ≤ n^2/3)
    (hf : ∀ e ∈ s, 0 ≤ f e)
    (hb : ∀ e ∈ s, f e ≤ Real.exp (if same e then l else h)) :
    (∏ e ∈ s, f e) ≤ Real.exp ((n^2/12-n/2-j)*l) := by
  apply (product_exp_bound s f (fun e => if same e then l else h) hf hb).trans
  apply Real.exp_le_exp.mpr
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [nsmul_eq_mul]
  exact remaining_log_bound n j _ _ l h hl hh hslack hcount hcross

/-- For N≥1 a fixed derivative-order loss is absorbed in an exponential
linear cost. This is valid for the source Stokes count n=N-1. -/
theorem stokes_uniform_exponential_cost (N j l : ℝ)
    (hN : 1 ≤ N) (hj : 0 ≤ j) (hl : l < 0) :
    Real.exp (((N-1)^2/12-(N-1)/2-j)*l) ≤
      Real.exp ((-l)*(j+2/3)*N) * Real.exp (l/12*N^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hjN : j ≤ j*N := by nlinarith
  have hsign := mul_nonneg (neg_nonneg.mpr hl.le) (show 0 ≤ j*N-j+7/12 by linarith)
  nlinarith

end
end IsingBulk.Tail
