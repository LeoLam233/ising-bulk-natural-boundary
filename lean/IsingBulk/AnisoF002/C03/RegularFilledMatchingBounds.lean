import IsingBulk.AnisoF002.C03.RegularFilledMatching
import IsingBulk.AnisoF002.C03.IsotropicOneSidedContraction

/-!
# Complete weighted matching bounds with every angular collision restored

These inequalities apply directly to the original canceled pair. They
are valid for arbitrary continued simple reciprocal roots, and the
physical interior specialization supplies its own root contraction.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open scoped BigOperators

theorem filled_pairs_even_weighted_bound {N : ℕ} (A B : ℂ) (r y : Fin N → ℂ)
    (hy : ∀ i, y i ≠ 0)
    (hp : ∀ i, r i ^ 2 - 2 * (A - B * (y i + (y i)⁻¹) / 2) * r i + 1 = 0)
    (hd : ∀ i j, 1 - r i * r j ≠ 0)
    (w : Fin N → ℝ) (hw : ∀ i, 0 < w i) {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hK : ∀ i j, ‖schur (r i) (r j)‖ ≤ q)
    (hP : ∀ i j, ‖canceledPair B (r i) (r j) (y i) (y j)‖ ≤ C * w i * w j)
    (n : ℕ) (xs : List (Fin N)) (hlen : xs.length = 2 * n) :
    ‖pairProductOn (fun i j => canceledPair B (r i) (r j) (y i) (y j)) xs‖ ≤
      (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)) * (xs.map w).prod := by
  rw [filled_pairs_even_matched_identity A B r y hy hp hd n xs hlen]
  exact matchedExpansion_weighted_norm_le _ _ w hw hq hC hK hP n xs hlen

theorem filled_pairs_odd_weighted_bound {N : ℕ} (A B : ℂ) (r y : Fin N → ℂ)
    (hy : ∀ i, y i ≠ 0)
    (hp : ∀ i, r i ^ 2 - 2 * (A - B * (y i + (y i)⁻¹) / 2) * r i + 1 = 0)
    (hd : ∀ i j, 1 - r i * r j ≠ 0)
    (w : Fin N → ℝ) (hw : ∀ i, 1 ≤ w i) {q C : ℝ} (hq : 1 ≤ q) (hC : 1 ≤ C)
    (hK : ∀ i j, ‖schur (r i) (r j)‖ ≤ q)
    (hP : ∀ i j, ‖canceledPair B (r i) (r j) (y i) (y j)‖ ≤ C * w i * w j)
    (n : ℕ) (xs : List (Fin N)) (hlen : xs.length = 2 * n + 1) :
    ‖pairProductOn (fun i j => canceledPair B (r i) (r j) (y i) (y j)) xs‖ ≤
      (matchingNumber (n + 1) : ℝ) * C ^ (n + 1) * q ^ (2 * (n + 1) * n) * (xs.map w).prod := by
  rw [filled_pairs_odd_matched_identity A B r y hy hp hd n xs hlen]
  let wg : Option (Fin N) → ℝ := fun a => match a with
    | none => 1
    | some i => w i
  have hwg (a : Option (Fin N)) : 0 < wg a := by
    cases a
    · norm_num [wg]
    · exact zero_lt_one.trans_le (hw _)
  have hKg (a b : Option (Fin N)) :
      ‖ghostKernel (fun i j => schur (r i) (r j)) 1 a b‖ ≤ q := by
    cases a <;> cases b <;> simp [ghostKernel, hq, (zero_le_one.trans hq), hK]
  have hPg (a b : Option (Fin N)) :
      ‖ghostCompletePair (fun i j => canceledPair B (r i) (r j) (y i) (y j)) a b‖ ≤
        C * wg a * wg b := by
    cases a <;> cases b
    · simpa only [ghostCompletePair, norm_zero, wg, mul_one] using zero_le_one.trans hC
    · rename_i i
      simp only [ghostCompletePair, norm_one, wg, mul_one]
      nlinarith [hw i]
    · rename_i i
      simp only [ghostCompletePair, norm_one, wg, mul_one]
      nlinarith [hw i]
    · exact hP _ _
  have hlen' : (xs.map some ++ [none]).length = 2 * (n + 1) := by simp [hlen]; omega
  have hb := matchedExpansion_weighted_norm_le _ _ wg hwg (zero_le_one.trans hq)
    (zero_le_one.trans hC) hKg hPg (n + 1) (xs.map some ++ [none]) hlen'
  simpa only [List.map_append, List.map_map, Function.comp_def, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, wg,
    one_mul, mul_one, Nat.add_sub_cancel] using hb

theorem complex_cos_exp_inverse (w : ℂ) :
    (Complex.exp (w * Complex.I) + (Complex.exp (w * Complex.I))⁻¹) / 2 = Complex.cos w := by
  have he := Complex.two_cos w
  rw [neg_mul, Complex.exp_neg] at he
  linear_combination -he / 2

end
end IsingBulk.AnisoF002.RegularTail.C03

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped BigOperators

theorem isotropic_complete_pairs_even_weighted (S : ℂ) (n : ℕ) (w : Fin (2 * n) → ℂ)
    (hW : ∀ i, 0 < (isotropicDispersion (S, w i)).im)
    (v : Fin (2 * n) → ℝ) (hv : ∀ i, 0 < v i) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ i j, ‖canceledPair 1 (isotropicInteriorRoot (S, w i)) (isotropicInteriorRoot (S, w j))
      (Complex.exp (w i * Complex.I)) (Complex.exp (w j * Complex.I))‖ ≤ C * v i * v j) :
    ‖∏ ij ∈ indexPairs (2 * n), canceledPair 1
      (isotropicInteriorRoot (S, w ij.1)) (isotropicInteriorRoot (S, w ij.2))
      (Complex.exp (w ij.1 * Complex.I)) (Complex.exp (w ij.2 * Complex.I))‖ ≤
      (matchingNumber n : ℝ) * C ^ n * ∏ i, v i := by
  have hp (i) : isotropicInteriorRoot (S, w i) ^ 2 - 2 *
      (S - 1 * (Complex.exp (w i * Complex.I) + (Complex.exp (w i * Complex.I))⁻¹) / 2) *
        isotropicInteriorRoot (S, w i) + 1 = 0 := by
    rw [one_mul, complex_cos_exp_inverse]
    exact isotropicInteriorRoot_polynomial _
  have hb := filled_pairs_even_weighted_bound S 1 (fun i => isotropicInteriorRoot (S, w i))
    (fun i => Complex.exp (w i * Complex.I)) (fun _ => Complex.exp_ne_zero _) hp
    (fun i j => upperEdgeRoot_pair_denominator (Or.inl (hW i)) (Or.inl (hW j))) v hv
    (q := 1) zero_le_one hC
    (fun i j => schur_norm_le_one_closed_lower _ _
      (upperEdgeRoot_norm_le_one (Or.inl (hW i))) (upperEdgeRoot_norm_le_one (Or.inl (hW j)))
      (upperEdgeRoot_im_neg (Or.inl (hW i))).le (upperEdgeRoot_im_neg (Or.inl (hW j))).le)
    hP n (List.ofFn id) (by simp)
  simpa only [pairProductOn_indexPairs, id_eq, List.map_ofFn, List.prod_ofFn,
    Function.comp_def, one_pow, mul_one] using hb

theorem isotropic_complete_pairs_odd_weighted (S : ℂ) (n : ℕ) (w : Fin (2 * n + 1) → ℂ)
    (hW : ∀ i, 0 < (isotropicDispersion (S, w i)).im)
    (v : Fin (2 * n + 1) → ℝ) (hv : ∀ i, 1 ≤ v i) {C : ℝ} (hC : 1 ≤ C)
    (hP : ∀ i j, ‖canceledPair 1 (isotropicInteriorRoot (S, w i)) (isotropicInteriorRoot (S, w j))
      (Complex.exp (w i * Complex.I)) (Complex.exp (w j * Complex.I))‖ ≤ C * v i * v j) :
    ‖∏ ij ∈ indexPairs (2 * n + 1), canceledPair 1
      (isotropicInteriorRoot (S, w ij.1)) (isotropicInteriorRoot (S, w ij.2))
      (Complex.exp (w ij.1 * Complex.I)) (Complex.exp (w ij.2 * Complex.I))‖ ≤
      (matchingNumber (n + 1) : ℝ) * C ^ (n + 1) * ∏ i, v i := by
  have hp (i) : isotropicInteriorRoot (S, w i) ^ 2 - 2 *
      (S - 1 * (Complex.exp (w i * Complex.I) + (Complex.exp (w i * Complex.I))⁻¹) / 2) *
        isotropicInteriorRoot (S, w i) + 1 = 0 := by
    rw [one_mul, complex_cos_exp_inverse]
    exact isotropicInteriorRoot_polynomial _
  have hb := filled_pairs_odd_weighted_bound S 1 (fun i => isotropicInteriorRoot (S, w i))
    (fun i => Complex.exp (w i * Complex.I)) (fun _ => Complex.exp_ne_zero _) hp
    (fun i j => upperEdgeRoot_pair_denominator (Or.inl (hW i)) (Or.inl (hW j))) v hv
    (q := 1) le_rfl hC
    (fun i j => schur_norm_le_one_closed_lower _ _
      (upperEdgeRoot_norm_le_one (Or.inl (hW i))) (upperEdgeRoot_norm_le_one (Or.inl (hW j)))
      (upperEdgeRoot_im_neg (Or.inl (hW i))).le (upperEdgeRoot_im_neg (Or.inl (hW j))).le)
    hP n (List.ofFn id) (by simp)
  simpa only [pairProductOn_indexPairs, id_eq, List.map_ofFn, List.prod_ofFn,
    Function.comp_def, one_pow, mul_one] using hb

end
end IsingBulk.AnisoF002.Isotropic
