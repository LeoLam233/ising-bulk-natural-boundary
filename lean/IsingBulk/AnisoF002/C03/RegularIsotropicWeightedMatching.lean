import IsingBulk.AnisoF002.C03.RegularSchur

/-!
# Vertex-weighted matching for the complete isotropic mixed pairs

Each matched vertex pays its weight exactly once. This is the finite
algebra that limits the exceptional opposite-branch cost to half the
number of branch coordinates, in both particle parities. No strict
root contraction and no division by a root difference are required.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
variable {α : Type*}

theorem matchedExpansion_diagonal (K P : α → α → ℂ) (c : α → ℂ)
    (n : ℕ) (xs : List α) (hlen : xs.length = 2 * n) :
    matchedExpansion K (fun a b => c a * c b * P a b) n xs =
      (xs.map c).prod * matchedExpansion K P n xs := by
  induction n generalizing xs with
  | zero =>
      have he : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      simp [he, matchedExpansion]
  | succ n ih =>
      cases xs with
      | nil => simp at hlen
      | cons a xs =>
          rw [matchedExpansion, matchedExpansion, ← List.sum_map_mul_left]
          apply congrArg List.sum
          apply List.map_congr_left
          intro bj hbj
          have hj := (List.mem_zipIdx' hbj).1
          have hb := (List.mem_zipIdx' hbj).2
          have hl : (xs.eraseIdx bj.2).length = 2 * n := by
            rw [List.length_eraseIdx_of_lt hj]
            simp only [List.length_cons] at hlen
            omega
          rw [ih _ hl, List.map_cons, List.prod_cons,
            map_prod_eraseIdx c xs bj.2 hj, ← hb]
          ring

theorem norm_real_weight_product (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (xs : List α) :
    ‖(xs.map (fun a => (w a : ℂ))).prod‖ = (xs.map w).prod := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.prod_cons, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (hw a), ih]

theorem matchedExpansion_weighted_norm_le (K P : α → α → ℂ)
    (w : α → ℝ) (hw : ∀ a, 0 < w a) {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hK : ∀ a b, ‖K a b‖ ≤ q)
    (hP : ∀ a b, ‖P a b‖ ≤ C * w a * w b)
    (n : ℕ) (xs : List α) (hlen : xs.length = 2 * n) :
    ‖matchedExpansion K P n xs‖ ≤
      (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)) * (xs.map w).prod := by
  let c : α → ℂ := fun a => (w a : ℂ)
  let P0 : α → α → ℂ := fun a b => P a b / (c a * c b)
  have hcz (a : α) : c a ≠ 0 := by
    change (w a : ℂ) ≠ 0
    exact_mod_cast (hw a).ne'
  have he : P = fun a b => c a * c b * P0 a b := by
    funext a b
    dsimp only [P0]
    field_simp [hcz a, hcz b]
  have hP0 (a b : α) : ‖P0 a b‖ ≤ C := by
    dsimp only [P0, c]
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (hw a).le, Real.norm_of_nonneg (hw b).le]
    apply (div_le_iff₀ (mul_pos (hw a) (hw b))).mpr
    simpa only [mul_assoc] using hP a b
  have hb := matchedExpansion_norm_le K P0 hq hC hK hP0 n xs hlen
  rw [he, matchedExpansion_diagonal K P0 c n xs hlen, norm_mul,
    norm_real_weight_product w (fun a => (hw a).le)]
  have hp : 0 ≤ (xs.map w).prod := List.prod_nonneg (fun a ha => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact (hw b).le)
  exact (mul_le_mul_of_nonneg_left hb hp).trans_eq (mul_comm _ _)

theorem paired_product_even_weighted_norm_le (K Y : α → α → ℂ)
    (hskew : ∀ a b, K a b = -K b a)
    (w : α → ℝ) (hw : ∀ a, 0 < w a) {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hK : ∀ a b, ‖K a b‖ ≤ q)
    (hP : ∀ a b, ‖K a b * Y a b‖ ≤ C * w a * w b)
    (n : ℕ) (xs : List α) (hlen : xs.length = 2 * n)
    (hpf : pfaffianOn Y n xs = pairProductOn Y xs) :
    ‖pairProductOn (fun a b => K a b * Y a b) xs‖ ≤
      (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)) * (xs.map w).prod := by
  rw [pairProductOn_mul, ← hpf, pairProduct_mul_pfaffian_eq_matched K Y hskew n xs hlen]
  exact matchedExpansion_weighted_norm_le K (fun a b => K a b * Y a b)
    w hw hq hC hK hP n xs hlen

theorem paired_product_odd_weighted_norm_le (K Y : α → α → ℂ)
    (hskew : ∀ a b, K a b = -K b a)
    (w : α → ℝ) (hw : ∀ a, 1 ≤ w a) {q C : ℝ} (hq : 1 ≤ q) (hC : 1 ≤ C)
    (hK : ∀ a b, ‖K a b‖ ≤ q)
    (hP : ∀ a b, ‖K a b * Y a b‖ ≤ C * w a * w b)
    (n : ℕ) (xs : List α) (hlen : xs.length = 2 * n + 1)
    (hpf : pfaffianOn (ghostKernel Y 1) (n + 1) (xs.map some ++ [none]) =
      pairProductOn Y xs) :
    ‖pairProductOn (fun a b => K a b * Y a b) xs‖ ≤
      (matchingNumber (n + 1) : ℝ) * C ^ (n + 1) * q ^ (2 * (n + 1) * n) * (xs.map w).prod := by
  let wg : Option α → ℝ := fun a => match a with
    | none => 1
    | some a => w a
  let Kg := ghostKernel K 1
  let Yg := ghostKernel Y 1
  let ys := xs.map some ++ [none]
  have hl : ys.length = 2 * (n + 1) := by simp [ys, hlen]; omega
  have hwg (a : Option α) : 0 < wg a := by
    cases a
    · norm_num [wg]
    · exact zero_lt_one.trans_le (hw _)
  have hKg (a b : Option α) : ‖Kg a b‖ ≤ q := by
    cases a <;> cases b <;> simp [Kg, ghostKernel, hq, (zero_le_one.trans hq), hK]
  have hPg (a b : Option α) : ‖Kg a b * Yg a b‖ ≤ C * wg a * wg b := by
    cases a <;> cases b
    · simp [Kg, Yg, ghostKernel, wg, (zero_le_one.trans hC)]
    · rename_i a
      simp only [Kg, Yg, ghostKernel, neg_mul_neg, one_mul, norm_one, wg]
      nlinarith [hw a]
    · rename_i a
      simp only [Kg, Yg, ghostKernel, mul_one, norm_one, wg]
      nlinarith [hw a]
    · exact hP _ _
  have hb := matchedExpansion_weighted_norm_le Kg (fun a b => Kg a b * Yg a b)
    wg hwg (zero_le_one.trans hq) (zero_le_one.trans hC) hKg hPg (n + 1) ys hl
  rw [← pairProduct_mul_pfaffian_eq_matched Kg Yg (ghostKernel_skew K 1 hskew) (n + 1) ys hl] at hb
  have hprodK : pairProductOn Kg ys = pairProductOn K xs := by
    simpa only [one_pow, one_mul] using pairProductOn_ghost K (1 : ℂ) xs
  have hprodw : (ys.map wg).prod = (xs.map w).prod := by
    simp [ys, List.map_map, Function.comp_def, wg]
  rw [hprodK, hpf, ← pairProductOn_mul, hprodw, Nat.add_sub_cancel] at hb
  exact hb

end
end IsingBulk.AnisoF002.RegularTail.C03
