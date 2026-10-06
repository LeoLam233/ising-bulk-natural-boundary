import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Algebraic and numerical substeps of the global tail sectors. These lemmas
are not the sector-integral propositions: they expose the exact collision
power, mixed transport identities, and protected-disk sheet margin. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

/-- The source collision exponent, with natural subtraction justified below. -/
def collisionPower (N j : ℕ) : ℕ := N^2 - 2*j - 4

/-- Both near-equality coarea arguments use the higher-even-order gap of two.
The actual source order `(2*p)^2/2-1` occurs here, not an independent bound. -/
theorem collisionPower_source_lower {p N j : ℕ} (hp : 1 ≤ p)
    (hN : 2*p+2 ≤ N) (hj : j ≤ (2*p)^2/2-1) :
    4*(2*p)+2 ≤ collisionPower N j := by
  have hsq : 2 ≤ (2*p)^2 := by nlinarith
  have hj' : 2*j+2 ≤ (2*p)^2 := by omega
  have hgap : (2*p)^2+4*(2*p)+4 ≤ N^2 := by nlinarith
  unfold collisionPower
  omega

theorem collisionPower_source_pos {p N j : ℕ} (hp : 1 ≤ p)
    (hN : 2*p+2 ≤ N) (hj : j ≤ (2*p)^2/2-1) :
    0 < collisionPower N j := by
  have := collisionPower_source_lower hp hN hj
  omega

/-- Exact no-truncation identity for the power surviving coarea. -/
theorem collisionPower_source_identity {p N j : ℕ} (hp : 1 ≤ p)
    (hN : 2*p+2 ≤ N) (hj : j ≤ (2*p)^2/2-1) :
    collisionPower N j + 2*j+4 = N^2 := by
  have hsq : 2 ≤ (2*p)^2 := by nlinarith
  have hj' : 2*j+2 ≤ (2*p)^2 := by omega
  have hgap : (2*p)^2+4*(2*p)+4 ≤ N^2 := by nlinarith
  unfold collisionPower
  omega

/-- The mixed field is kept unfactored. The compact anchor lies outside J. -/
def mixedVelocity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (a : ι → ℂ) (j q : ι) (X : ℂ) (i : ι) : ℂ :=
  (if i ∈ J then a i else 0) + (if i = j then X else 0) -
    (if i = q then (∑ l ∈ J, a l)+X else 0)

/-- The first global phase is frozen exactly, with no occupancy treated as
an independent variable. -/
theorem mixedVelocity_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (a : ι → ℂ) (j q : ι) (X : ℂ) :
    ∑ i, mixedVelocity J a j q X i = 0 := by
  simp [mixedVelocity, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Weighted sum before solving the two-phase transport equation. -/
theorem mixedVelocity_weighted_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (a b : ι → ℂ) (j q : ι) (X : ℂ) :
    ∑ i, b i*mixedVelocity J a j q X i =
      (∑ i ∈ J, b i*a i) + (b j-b q)*X-b q*(∑ i ∈ J, a i) := by
  simp only [mixedVelocity, mul_sub, mul_add, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_ite, mul_zero]
  simp only [Finset.sum_ite_mem, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.univ_inter]
  ring

/-- The source formula freezes the second global phase exactly. -/
theorem mixedVelocity_freezes_second {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (a b : ι → ℂ) (j q : ι) (D : ℂ)
    (hsep : b j-b q ≠ 0) :
    ∑ i, b i*mixedVelocity J a j q ((D+b q*(∑ l ∈ J, a l))/(b j-b q)) i =
      D + ∑ i ∈ J, b i*a i := by
  rw [mixedVelocity_weighted_sum]
  field_simp
  ring

/-- A nonselected true-branch coordinate is frozen individually. -/
theorem mixedVelocity_other_branch {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (a : ι → ℂ) (j q : ι) (X : ℂ) {i : ι}
    (hi : i ∈ J) (hij : i ≠ j) (hq : q ∉ J) :
    mixedVelocity J a j q X i = a i := by
  have hiq : i ≠ q := by intro h; subst i; exact hq hi
  simp [mixedVelocity, hi, hij, hiq]

/-- On true plateaus all occupancy directional derivatives are zero termwise.
This identity does not assume the occupancy itself is constant globally. -/
theorem mixedVelocity_preserves_plateau {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Finset ι) (a d : ι → ℂ) (j q : ι) (X : ℂ)
    (hj : j ∈ J) (hJ : ∀ i ∈ J, d i = 0) (hq : d q = 0) :
    ∑ i, d i*mixedVelocity J a j q X i = 0 := by
  rw [mixedVelocity_weighted_sum]
  simp only [hJ j hj, hq, sub_self, zero_mul, sub_zero, add_zero]
  exact Finset.sum_eq_zero (fun i hi => by rw [hJ i hi]; simp)

/-- The residual phase velocity is regular in the reciprocal branch slope. -/
theorem mixed_residual_reciprocal (D A bj bq : ℂ) (hb : bj ≠ 0)
    (hsep : bj-bq ≠ 0) :
    -bj*((D+bq*A)/(bj-bq)) = -(D+bq*A)/(1-bq/bj) := by
  field_simp

/-- The fixed one-quarter support condition provides a genuine denominator
margin, rather than merely a pointwise nonzero denominator. -/
theorem mixed_denominator_margin {r : ℂ} (hr : ‖r‖ ≤ (1/4:ℝ)) :
    (3/4:ℝ) ≤ ‖1-r‖ := by
  have h := norm_sub_norm_le (1:ℂ) r
  norm_num at h
  linarith

/-- The protected radius is reduced after the deformation margin is chosen.
This is uniform in dimension, lambda and the coupled occupancy. -/
theorem protected_radius_le {N : ℕ} (hN : 1 ≤ N) {c lamStar lam P : ℝ}
    (hc : 0 ≤ c) (hs : 0 ≤ lamStar) (hlam : lamStar ≤ lam) (hP : 1 ≤ P) :
    c*lamStar/(N:ℝ)^2 ≤ c*(lam*P/(N:ℝ))/(N:ℝ) := by
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 ≤ lam := hs.trans hlam
  have hp : lamStar ≤ lam*P := by nlinarith
  calc
    c*lamStar/(N:ℝ)^2 ≤ c*(lam*P)/(N:ℝ)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc) (sq_nonneg _)
    _ = _ := by field_simp

/-- The sheet condition survives a reserved quarter of the imaginary margin. -/
theorem protected_imaginary_margin {W W₀ : ℂ} {b eps t : ℝ}
    (hb : 0 < b) (heps : 0 < eps) (ht : 0 ≤ t)
    (hcenter : b*(eps+t) ≤ W₀.im)
    (hmove : ‖W-W₀‖ ≤ b*(eps+t)/4) :
    (3/4)*b*(eps+t) ≤ W.im ∧ 0 < W.im := by
  have hi : |W.im-W₀.im| ≤ ‖W-W₀‖ := by
    simpa only [Complex.sub_im] using Complex.abs_im_le_norm (W-W₀)
  have hl := (abs_le.mp (hi.trans hmove)).1
  have hmargin : (3/4)*b*(eps+t) ≤ W.im := by linarith
  exact ⟨hmargin, lt_of_lt_of_le (by positivity) hmargin⟩

/-- The actual all-branch mean and Euclidean full-equality radius. -/
def branchMean {N : ℕ} (u : Fin N → ℝ) : ℝ := (∑ i, u i)/(N:ℝ)
def branchShapeRadius {N : ℕ} (u : Fin N → ℝ) : ℝ :=
  Real.sqrt (∑ i, (u i-branchMean u)^2)

theorem deviation_le_branchShapeRadius {N : ℕ} (u : Fin N → ℝ) (i : Fin N) :
    |u i-branchMean u| ≤ branchShapeRadius u := by
  have hsum : 0 ≤ ∑ i, (u i-branchMean u)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hi : (u i-branchMean u)^2 ≤ ∑ i, (u i-branchMean u)^2 :=
    Finset.single_le_sum (f := fun l : Fin N => (u l-branchMean u)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hs := Real.sq_sqrt hsum
  have hr := Real.sqrt_nonneg (∑ i, (u i-branchMean u)^2)
  unfold branchShapeRadius
  nlinarith [sq_abs (u i-branchMean u),abs_nonneg (u i-branchMean u)]

/-- Exact support inclusion used before the near-equality coarea argument.
The anchor and scale inclusion imply a common sign for every coordinate. -/
theorem near_equality_anchor_common_sign {N : ℕ} (u : Fin N → ℝ) (a : Fin N)
    {b : ℝ} (_hb : 0 < b) (ha : b/2 ≤ |u a|)
    (hr : branchShapeRadius u ≤ b/8) :
    (3*b/8 ≤ branchMean u ∧ ∀ i, b/4 ≤ u i) ∨
      (branchMean u ≤ -(3*b/8) ∧ ∀ i, u i ≤ -(b/4)) := by
  have hdev (i : Fin N) := abs_le.mp ((deviation_le_branchShapeRadius u i).trans hr)
  rcases le_total 0 (u a) with hpos | hneg
  · rw [abs_of_nonneg hpos] at ha
    left
    constructor
    · linarith [(hdev a).2]
    · intro i
      linarith [(hdev a).2,(hdev i).1]
  · rw [abs_of_nonpos hneg] at ha
    right
    constructor
    · linarith [(hdev a).1]
    · intro i
      linarith [(hdev a).1,(hdev i).2]

/-- No coordinate can approach the branch point on the near-equality
anchor sector; this is uniform in N and epsilon. -/
theorem near_equality_anchor_separated {N : ℕ} (u : Fin N → ℝ) (a : Fin N)
    {b : ℝ} (hb : 0 < b) (ha : b/2 ≤ |u a|)
    (hr : branchShapeRadius u ≤ b/8) : ∀ i, b/4 ≤ |u i| := by
  rcases near_equality_anchor_common_sign u a hb ha hr with h | h
  · intro i
    exact (h.2 i).trans (le_abs_self _)
  · intro i
    have hi := h.2 i
    have hi' := neg_le_abs (u i)
    linarith

end
end IsingBulk.Tail
