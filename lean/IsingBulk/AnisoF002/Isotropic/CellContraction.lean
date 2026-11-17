import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# F002: finite-cell counting and a Gaussian product bound

The finite-cell mechanism of `lem:iso-cell-gaussian` is proved for an
arbitrary finite collection with an explicit cell assignment.  The analytic
construction of the common neighborhood for the actual complete pair is
not assumed to follow from this combinatorial theorem.
-/
namespace IsingBulk.AnisoF002.Isotropic

open scoped BigOperators

/-- Each unordered pair is counted once. -/
def indexPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  (Finset.univ ×ˢ Finset.univ).filter fun ij => ij.1 < ij.2

/-- A concrete finite cell population. -/
def population {N K : ℕ} (c : Fin N → Fin K) (a : Fin K) : ℕ :=
  (Finset.univ.filter fun i => c i = a).card

/-- The retained same-cell pairs. -/
def sameCellPairs {N K : ℕ} (c : Fin N → Fin K) : Finset (Fin N × Fin N) :=
  (indexPairs N).filter fun ij => c ij.1 = c ij.2

theorem card_indexPairs (N : ℕ) : (indexPairs N).card = N.choose 2 := by
  simpa [indexPairs] using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin N))))

theorem sum_population {N K : ℕ} (c : Fin N → Fin K) :
    (∑ a, population c a) = N := by
  simpa [population] using
    (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin N)))
      (t := (Finset.univ : Finset (Fin K))) (f := c) (by simp)).symm

theorem card_sameCellPairs {N K : ℕ} (c : Fin N → Fin K) :
    (sameCellPairs c).card = ∑ a, (population c a).choose 2 := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := sameCellPairs c) (t := (Finset.univ : Finset (Fin K)))
    (f := fun ij : Fin N × Fin N => c ij.1) (by simp)
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  have heq : (sameCellPairs c).filter (fun ij => c ij.1 = a) =
      ((Finset.univ.filter fun i => c i = a) ×ˢ
       (Finset.univ.filter fun i => c i = a)).filter (fun ij => ij.1 < ij.2) := by
    ext ij
    simp only [sameCellPairs, indexPairs, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    aesop
  rw [heq, Finset.card_product_filter_lt]
  rfl

/-- Exact same-cell pair count in real arithmetic, including empty cells. -/
theorem sameCellPairs_real_count {N K : ℕ} (c : Fin N → Fin K) :
    ((sameCellPairs c).card : ℝ) =
      ((∑ a, (population c a : ℝ) ^ 2) - N) / 2 := by
  rw [card_sameCellPairs, Nat.cast_sum]
  simp only [Nat.cast_choose_two]
  have hs : (∑ a, (population c a : ℝ)) = (N : ℝ) := by
    exact_mod_cast sum_population c
  calc
    (∑ a, (population c a : ℝ) * ((population c a : ℝ) - 1) / 2) =
        ((∑ a, (population c a : ℝ) ^ 2) - ∑ a, (population c a : ℝ)) / 2 := by
      simp only [← Finset.sum_div, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [hs]

/-- The quadratic number of same-cell pairs is the source of Gaussian decay. -/
theorem sameCellPairs_lower {N K : ℕ} (c : Fin N → Fin K) (hK : 0 < K) :
    ((N : ℝ) ^ 2 / K - N) / 2 ≤ ((sameCellPairs c).card : ℝ) := by
  have hs : (∑ a, (population c a : ℝ)) = (N : ℝ) := by
    exact_mod_cast sum_population c
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin K)) (fun a => (population c a : ℝ)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  rw [hs] at hcs
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hd : (N : ℝ) ^ 2 / K ≤ ∑ a, (population c a : ℝ) ^ 2 :=
    (div_le_iff₀ hKr).mpr hcs
  rw [sameCellPairs_real_count]
  linarith

/-- A finite-cell exponential envelope, retaining every complete pair. -/
theorem complete_pair_product_bound {N K : ℕ} (c : Fin N → Fin K)
    (P : Fin N → Fin N → ℂ) (a b : ℝ) (hK : 0 < K)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hwithin : ∀ i j, i < j → c i = c j → ‖P i j‖ ≤ Real.exp (-a))
    (hall : ∀ i j, i < j → ‖P i j‖ ≤ Real.exp b) :
    ‖∏ ij ∈ indexPairs N, P ij.1 ij.2‖ ≤
      Real.exp (-(a + b - K * b) / (2 * K) * (N : ℝ) ^ 2 + a / 2 * N) := by
  let w : Fin N × Fin N → ℝ := fun ij => if c ij.1 = c ij.2 then -a else b
  have hp : ‖∏ ij ∈ indexPairs N, P ij.1 ij.2‖ ≤
      ∏ ij ∈ indexPairs N, Real.exp (w ij) := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro ij hij
    have hij' : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
    simp only [w]
    split_ifs with hc
    · exact hwithin ij.1 ij.2 hij' hc
    · exact hall ij.1 ij.2 hij'
  rw [← Real.exp_sum] at hp
  have hw : (∑ ij ∈ indexPairs N, w ij) =
      b * (indexPairs N).card - (a + b) * (sameCellPairs c).card := by
    have hwi : ∀ ij, w ij = b - (a + b) * (if c ij.1 = c ij.2 then (1 : ℝ) else 0) := by
      intro ij
      simp only [w]
      split_ifs <;> ring
    simp_rw [hwi]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_boole]
    simp only [sameCellPairs]
    ring
  have hc := sameCellPairs_lower c hK
  have hn : ((indexPairs N).card : ℝ) = (N : ℝ) * (N - 1) / 2 := by
    rw [card_indexPairs, Nat.cast_choose_two]
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  refine hp.trans (Real.exp_le_exp.mpr ?_)
  rw [hw, hn]
  have hm := mul_le_mul_of_nonneg_left hc (add_nonneg ha hb)
  have he : b * ((N : ℝ) * (N - 1) / 2) -
      (a + b) * (((N : ℝ)^2 / K - N) / 2) =
      -(a + b - K * b) / (2 * K) * (N : ℝ) ^ 2 + a / 2 * N := by
    field_simp
    ring
  rw [← he]
  linarith

end IsingBulk.AnisoF002.Isotropic
