import IsingBulk.AnisoF002.C03.NegativeGlobalAttenuation
import Mathlib.Algebra.Order.Chebyshev

/-!
# A global odd-particle momentum gap on the real cycle

This proof keeps the original zero-sum momentum constraint.  Multiplying
the shifted unit phases gives -1 for every odd population, so the total
cosine distance from the negative collision is bounded below by 2/N.
No winding sector, angle chart, or particle competitor is discarded.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem unit_product_distance_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ = 1) :
    ‖(∏ i ∈ s, f i) - 1‖ ≤ ∑ i ∈ s, ‖f i - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, ‖f i‖ = 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    calc
      ‖f a * (∏ i ∈ s, f i) - 1‖ =
          ‖f a * ((∏ i ∈ s, f i) - 1) + (f a - 1)‖ := by congr 1; ring
      _ ≤ ‖f a * ((∏ i ∈ s, f i) - 1)‖ + ‖f a - 1‖ := norm_add_le _ _
      _ = ‖(∏ i ∈ s, f i) - 1‖ + ‖f a - 1‖ := by rw [norm_mul, hfa, one_mul]
      _ ≤ (∑ i ∈ s, ‖f i - 1‖) + ‖f a - 1‖ := add_le_add (ih hfs) le_rfl
      _ = _ := by ring

theorem norm_unit_phase_sub_one_sq (q : ℝ) :
    ‖Complex.exp ((q : ℂ) * Complex.I) - 1‖ ^ 2 = 2 * (1 - Real.cos q) := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, sub_zero, Complex.exp_re, Complex.exp_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_self, Real.exp_zero, one_mul, mul_one, add_zero]
  nlinarith [Real.sin_sq_add_cos_sq q]

theorem cosine_gap_of_unit_product {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hprod : (∏ i, Complex.exp ((q i : ℂ) * Complex.I)) = -1) :
    2 / (n : ℝ) ≤ ∑ i, (1 - Real.cos (q i)) := by
  have hu : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ‖Complex.exp ((q i : ℂ) * Complex.I)‖ = 1 := by
    intro i _
    rw [Complex.norm_exp]
    simp
  have hnorm := unit_product_distance_le_sum Finset.univ
    (fun i => Complex.exp ((q i : ℂ) * Complex.I)) hu
  rw [hprod] at hnorm
  have htwo : (2 : ℝ) ≤ ∑ i, ‖Complex.exp ((q i : ℂ) * Complex.I) - 1‖ := by
    convert hnorm using 1
    norm_num
  have hCS := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => ‖Complex.exp ((q i : ℂ) * Complex.I) - 1‖)
  simp only [Finset.card_univ, Fintype.card_fin, norm_unit_phase_sub_one_sq,
    ← Finset.mul_sum] at hCS
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
  nlinarith

theorem shifted_odd_momentum_product {n : ℕ} (hn : Odd n) (q : Fin n → ℝ)
    (hq : ∑ i, q i = 0) :
    (∏ i, Complex.exp (((q i - Real.pi : ℝ) : ℂ) * Complex.I)) = -1 := by
  have hs : ∑ i, ((q i : ℂ) * Complex.I) = 0 := by
    rw [← Finset.sum_mul]
    have he : ∑ i, (q i : ℂ) = 0 := by exact_mod_cast hq
    rw [he, zero_mul]
  have hshift : ∀ i : Fin n,
      Complex.exp (((q i - Real.pi : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((q i : ℂ) * Complex.I) * (-1) := by
    intro i
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I]
    ring
  simp_rw [hshift]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hs, Complex.exp_zero]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul] using
    (hn.neg_one_pow : (-1 : ℂ) ^ n = -1)

theorem odd_zero_sum_negative_momentum_gap {n : ℕ} (hn : Odd n) (q : Fin n → ℝ)
    (hq : ∑ i, q i = 0) :
    2 / (n : ℝ) ≤ ∑ i, (1 + Real.cos (q i)) := by
  have hnpos : 0 < n := hn.pos
  have h := cosine_gap_of_unit_product hnpos (fun i => q i - Real.pi)
    (shifted_odd_momentum_product hn q hq)
  simpa only [Real.cos_sub_pi, sub_neg_eq_add] using h

end
end IsingBulk.AnisoF002.NegativeHT
