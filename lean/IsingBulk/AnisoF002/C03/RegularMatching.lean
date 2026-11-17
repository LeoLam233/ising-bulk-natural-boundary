import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Division-free matched expansion for F002 regular numerators

This is the finite all-order matching algebra required in frozen F002
Lemma 3.1.  The root and angular kernels are kept separate until a matched
edge is selected.  No root factor is divided out, so root coincidences
remain admissible.  No historical Ising theorem is used in this file.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section

variable {α R : Type*}

noncomputable def pairProductOn [CommRing R] (K : α → α → R) : List α → R
  | [] => 1
  | a :: xs => (xs.map (K a)).prod * pairProductOn K xs

noncomputable def pfaffianOn [CommRing R] (K : α → α → R) : ℕ → List α → R
  | 0, _ => 1
  | _ + 1, [] => 0
  | n + 1, a :: xs => (xs.zipIdx.map fun bj =>
      (-1 : R) ^ bj.2 * K a bj.1 * pfaffianOn K n (xs.eraseIdx bj.2)).sum

noncomputable def matchedExpansion (K P : α → α → ℂ) : ℕ → List α → ℂ
  | 0, _ => 1
  | _ + 1, [] => 0
  | n + 1, a :: xs => (xs.zipIdx.map fun bj =>
      P a bj.1 * ((xs.eraseIdx bj.2).map (fun c => K a c * K bj.1 c)).prod *
        matchedExpansion K P n (xs.eraseIdx bj.2)).sum

noncomputable def matchingNumber : ℕ → ℕ
  | 0 => 1
  | n + 1 => (2 * n + 1) * matchingNumber n

theorem map_prod_eraseIdx [CommRing R] (f : α → R)
    (xs : List α) (j : ℕ) (hj : j < xs.length) :
    (xs.map f).prod = f xs[j] * ((xs.eraseIdx j).map f).prod := by
  have h := List.CommMonoid.mul_prod_eraseIdx (l := xs.map f) (i := j)
    (by simpa using hj)
  simpa only [List.getElem_map, List.eraseIdx_map] using h.symm

theorem pairProductOn_eraseIdx [CommRing R] (K : α → α → R)
    (hK : ∀ a b, K a b = -K b a) (xs : List α)
    (j : ℕ) (hj : j < xs.length) :
    pairProductOn K xs = (-1 : R) ^ j *
      ((xs.eraseIdx j).map (K xs[j])).prod * pairProductOn K (xs.eraseIdx j) := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons a xs ih =>
    cases j with
    | zero => simp [pairProductOn]
    | succ j =>
      have hj' : j < xs.length := by simpa using hj
      simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ,
        List.map_cons, List.prod_cons, pairProductOn, pow_succ]
      rw [map_prod_eraseIdx (K a) xs j hj', ih j hj', hK a xs[j]]
      ring

theorem pairProductOn_cons_remove [CommRing R] (K : α → α → R)
    (hK : ∀ a b, K a b = -K b a) (a : α) (xs : List α)
    (j : ℕ) (hj : j < xs.length) :
    pairProductOn K (a :: xs) = (-1 : R) ^ j * K a xs[j] *
      ((xs.eraseIdx j).map (fun c => K a c * K xs[j] c)).prod *
        pairProductOn K (xs.eraseIdx j) := by
  rw [pairProductOn, map_prod_eraseIdx (K a) xs j hj,
    pairProductOn_eraseIdx K hK xs j hj, List.prod_map_mul]
  ring

theorem pairProductOn_mul [CommRing R] (K L : α → α → R) (xs : List α) :
    pairProductOn (fun a b => K a b * L a b) xs =
      pairProductOn K xs * pairProductOn L xs := by
  induction xs with
  | nil => simp [pairProductOn]
  | cons a xs ih =>
      simp only [pairProductOn, List.prod_map_mul, ih]
      ring

theorem pairProductOn_append_singleton [CommRing R] (K : α → α → R)
    (xs : List α) (g : α) :
    pairProductOn K (xs ++ [g]) =
      (xs.map (fun a => K a g)).prod * pairProductOn K xs := by
  induction xs with
  | nil => simp [pairProductOn]
  | cons a xs ih =>
      simp only [List.cons_append, pairProductOn, List.map_append, List.prod_append,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, ih]
      ring

theorem pairProductOn_map {β : Type*} [CommRing R] (K : β → β → R)
    (f : α → β) (xs : List α) :
    pairProductOn K (xs.map f) = pairProductOn (fun a b => K (f a) (f b)) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [pairProductOn, List.map_map, Function.comp_def, ih]

theorem pfaffianOn_diagonal [CommRing R] (K : α → α → R)
    (c : α → R) (n : ℕ) (xs : List α) (hlen : xs.length = 2 * n) :
    pfaffianOn (fun a b => c a * c b * K a b) n xs =
      (xs.map c).prod * pfaffianOn K n xs := by
  induction n generalizing xs with
  | zero =>
      have he : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      simp [he, pfaffianOn]
  | succ n ih =>
      cases xs with
      | nil => simp at hlen
      | cons a xs =>
          rw [pfaffianOn, pfaffianOn, ← List.sum_map_mul_left]
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

/-- A ghost is a distinguished algebraic label, not an extra particle. -/
def ghostKernel [CommRing R] (K : α → α → R) (s : R) : Option α → Option α → R
  | some a, some b => K a b
  | some _, none => s
  | none, some _ => -s
  | none, none => 0

theorem ghostKernel_skew [CommRing R] (K : α → α → R) (s : R)
    (hK : ∀ a b, K a b = -K b a) :
    ∀ a b, ghostKernel K s a b = -ghostKernel K s b a := by
  intro a b
  cases a <;> cases b
  · simp [ghostKernel]
  · simp [ghostKernel]
  · simp [ghostKernel]
  · exact hK _ _

theorem pairProductOn_ghost [CommRing R] (K : α → α → R)
    (s : R) (xs : List α) :
    pairProductOn (ghostKernel K s) (xs.map some ++ [none]) =
      s ^ xs.length * pairProductOn K xs := by
  rw [pairProductOn_append_singleton, pairProductOn_map, List.map_map]
  simp only [Function.comp_def, ghostKernel]
  simp

/-- Exact selected-edge cancellation at every size. The two alternating
signs cancel algebraically; there is no division by a root difference. -/
theorem pairProduct_mul_pfaffian_eq_matched
    (K Y : α → α → ℂ) (hK : ∀ a b, K a b = -K b a)
    (n : ℕ) (xs : List α) (hlen : xs.length = 2 * n) :
    pairProductOn K xs * pfaffianOn Y n xs =
      matchedExpansion K (fun a b => K a b * Y a b) n xs := by
  induction n generalizing xs with
  | zero =>
      have he : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      simp [he, pairProductOn, pfaffianOn, matchedExpansion]
  | succ n ih =>
      cases xs with
      | nil => simp at hlen
      | cons a xs =>
          rw [pfaffianOn, matchedExpansion, ← List.sum_map_mul_left]
          apply congrArg List.sum
          apply List.map_congr_left
          intro bj hbj
          have hj := (List.mem_zipIdx' hbj).1
          have hb := (List.mem_zipIdx' hbj).2
          have hl : (xs.eraseIdx bj.2).length = 2 * n := by
            rw [List.length_eraseIdx_of_lt hj]
            simp only [List.length_cons] at hlen
            omega
          rw [pairProductOn_cons_remove K hK a xs bj.2 hj, ← hb, ← ih _ hl]
          have hs : ((-1 : ℂ) ^ bj.2) ^ 2 = 1 := by
            rw [← pow_mul, Nat.mul_comm, pow_mul]
            norm_num
          linear_combination
            (K a bj.1 * Y a bj.1 *
              ((xs.eraseIdx bj.2).map (fun c => K a c * K bj.1 c)).prod *
                pairProductOn K (xs.eraseIdx bj.2) *
                  pfaffianOn Y n (xs.eraseIdx bj.2)) * hs

theorem norm_list_prod_le_pow (xs : List α) (f : α → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ a ∈ xs, ‖f a‖ ≤ C) :
    ‖(xs.map f).prod‖ ≤ C ^ xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, norm_mul, pow_succ]
      calc
        ‖f a‖ * ‖(xs.map f).prod‖ ≤ C * C ^ xs.length :=
          mul_le_mul (hf a (by simp))
            (ih (fun b hb => hf b (by simp [hb]))) (norm_nonneg _) hC
        _ = _ := by ring

theorem norm_list_sum_le_length (xs : List α) (f : α → ℂ) (C : ℝ)
    (hf : ∀ a ∈ xs, ‖f a‖ ≤ C) :
    ‖(xs.map f).sum‖ ≤ xs.length * C := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      calc
        ‖f a + (xs.map f).sum‖ ≤ ‖f a‖ + ‖(xs.map f).sum‖ := norm_add_le _ _
        _ ≤ C + xs.length * C := add_le_add (hf a (by simp))
          (ih (fun b hb => hf b (by simp [hb])))
        _ = _ := by ring

/-- The exact even matching bound, with `2*n*(n-1)` uncanceled root
factors. Its conditional kernel hypotheses will be instantiated on the
actual F002 root and complete canceled pair. -/
theorem matchedExpansion_norm_le (K P : α → α → ℂ)
    {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hK : ∀ a b, ‖K a b‖ ≤ q) (hP : ∀ a b, ‖P a b‖ ≤ C)
    (n : ℕ) (xs : List α) (hlen : xs.length = 2 * n) :
    ‖matchedExpansion K P n xs‖ ≤
      (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)) := by
  induction n generalizing xs with
  | zero => simp [matchedExpansion, matchingNumber]
  | succ n ih =>
      cases xs with
      | nil => simp at hlen
      | cons a xs =>
          have hlen' : xs.length = 2 * n + 1 := by
            simp only [List.length_cons] at hlen
            omega
          have hb : ∀ bj ∈ xs.zipIdx,
              ‖P a bj.1 * ((xs.eraseIdx bj.2).map
                (fun c => K a c * K bj.1 c)).prod *
                  matchedExpansion K P n (xs.eraseIdx bj.2)‖ ≤
                C * q ^ (4 * n) *
                  ((matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1))) := by
            intro bj hbj
            have hj := (List.mem_zipIdx' hbj).1
            have hl : (xs.eraseIdx bj.2).length = 2 * n := by
              rw [List.length_eraseIdx_of_lt hj, hlen']
              omega
            have hc := norm_list_prod_le_pow (xs.eraseIdx bj.2)
              (fun c => K a c * K bj.1 c) (mul_nonneg hq hq)
              (fun c _ => by
                rw [norm_mul]
                exact mul_le_mul (hK a c) (hK bj.1 c) (norm_nonneg _) hq)
            have hpow : (q * q) ^ (xs.eraseIdx bj.2).length = q ^ (4 * n) := by
              rw [hl, ← pow_two, ← pow_mul]
              congr 1
              omega
            rw [hpow] at hc
            rw [norm_mul, norm_mul]
            exact mul_le_mul (mul_le_mul (hP a bj.1) hc (norm_nonneg _ ) hC)
              (ih _ hl) (norm_nonneg _)
              (mul_nonneg hC (pow_nonneg hq _))
          rw [matchedExpansion]
          apply (norm_list_sum_le_length xs.zipIdx _ _ hb).trans_eq
          rw [List.length_zipIdx, hlen', matchingNumber]
          simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
            pow_succ, Nat.add_sub_cancel]
          have he : 4 * n + 2 * n * (n - 1) = 2 * (n + 1) * n := by
            cases n with
            | zero => simp
            | succ n => simp; ring
          calc
            _ = ((2 * n + 1 : ℕ) : ℝ) * matchingNumber n * (C ^ n * C) *
                q ^ (4 * n + 2 * n * (n - 1)) := by rw [pow_add]; push_cast; ring
            _ = _ := by rw [he]; push_cast; ring

/-- The even estimate in the form used by the actual Schur specialization. -/
theorem paired_product_even_norm_le (K Y : α → α → ℂ)
    (hskew : ∀ a b, K a b = -K b a)
    {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hK : ∀ a b, ‖K a b‖ ≤ q)
    (hP : ∀ a b, ‖K a b * Y a b‖ ≤ C)
    (n : ℕ) (xs : List α) (hlen : xs.length = 2 * n)
    (hpf : pfaffianOn Y n xs = pairProductOn Y xs) :
    ‖pairProductOn (fun a b => K a b * Y a b) xs‖ ≤
      (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)) := by
  rw [pairProductOn_mul, ← hpf, pairProduct_mul_pfaffian_eq_matched K Y hskew n xs hlen]
  exact matchedExpansion_norm_le K (fun a b => K a b * Y a b)
    hq hC hK hP n xs hlen

/-- Odd matching is reduced to the same even expansion by scaling the
single ghost row. It retains exactly `2*n*n = (N-1)^2/2` uncanceled root
factors and costs `(2*n+1)!!` matchings, with no division by a root value. -/
theorem paired_product_odd_norm_le (K Y : α → α → ℂ)
    (hskew : ∀ a b, K a b = -K b a)
    {q C : ℝ} (hq : 0 < q) (hC : 0 < C)
    (hK : ∀ a b, ‖K a b‖ ≤ q)
    (hP : ∀ a b, ‖K a b * Y a b‖ ≤ C)
    (n : ℕ) (xs : List α) (hlen : xs.length = 2 * n + 1)
    (hpf : pfaffianOn (ghostKernel Y 1) (n + 1) (xs.map some ++ [none]) =
      pairProductOn Y xs) :
    ‖pairProductOn (fun a b => K a b * Y a b) xs‖ ≤
      (matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n) := by
  let c : Option α → ℂ := fun a => match a with
    | some _ => 1
    | none => (C / q : ℝ)
  let Kg := ghostKernel K (q : ℂ)
  let Yg : Option α → Option α → ℂ := fun a b => c a * c b * ghostKernel Y 1 a b
  let ys := xs.map some ++ [none]
  have hl : ys.length = 2 * (n + 1) := by simp [ys, hlen]; omega
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hKg : ∀ a b, ‖Kg a b‖ ≤ q := by
    intro a b
    cases a <;> cases b <;> simp [Kg, ghostKernel, hq.le, hK, abs_of_pos hq]
  have hPg : ∀ a b, ‖Kg a b * Yg a b‖ ≤ C := by
    intro a b
    cases a <;> cases b
    · simp [Kg, Yg, ghostKernel, c, hC.le]
    · simp [Kg, Yg, ghostKernel, c, abs_of_pos hC, abs_of_pos hq]
      exact le_of_eq (mul_div_cancel₀ C hq.ne')
    · simp [Kg, Yg, ghostKernel, c, abs_of_pos hC, abs_of_pos hq]
      exact le_of_eq (mul_div_cancel₀ C hq.ne')
    · simpa [Kg, Yg, ghostKernel, c] using hP _ _
  have hb := matchedExpansion_norm_le Kg (fun a b => Kg a b * Yg a b)
    hq.le hC.le hKg hPg (n + 1) ys hl
  rw [← pairProduct_mul_pfaffian_eq_matched Kg Yg
    (ghostKernel_skew K (q : ℂ) hskew) (n + 1) ys hl] at hb
  have hpfg : pfaffianOn Yg (n + 1) ys =
      ((C / q : ℝ) : ℂ) * pairProductOn Y xs := by
    rw [show Yg = fun a b => c a * c b * ghostKernel Y 1 a b from rfl,
      pfaffianOn_diagonal _ c (n + 1) ys hl]
    have hprod : (ys.map c).prod = ((C / q : ℝ) : ℂ) := by
      simp [ys, List.map_map, Function.comp_def, c]
    rw [hprod]
    exact congrArg (((C / q : ℝ) : ℂ) * ·) hpf
  rw [hpfg, show pairProductOn Kg ys =
      (q : ℂ) ^ xs.length * pairProductOn K xs from pairProductOn_ghost K _ xs] at hb
  have hlhs : (q : ℂ) ^ xs.length * pairProductOn K xs *
      (((C / q : ℝ) : ℂ) * pairProductOn Y xs) =
        ((C * q ^ (2 * n) : ℝ) : ℂ) *
          pairProductOn (fun a b => K a b * Y a b) xs := by
    rw [hlen, pow_succ, pairProductOn_mul]
    push_cast
    field_simp
  rw [hlhs, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg hC.le (pow_nonneg hq.le _))] at hb
  have hrhs : (matchingNumber (n + 1) : ℝ) * C ^ (n + 1) *
      q ^ (2 * (n + 1) * ((n + 1) - 1)) =
        (C * q ^ (2 * n)) *
          ((matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n)) := by
    rw [Nat.add_sub_cancel, pow_succ,
      show 2 * (n + 1) * n = 2 * n + 2 * n * n by ring, pow_add]
    ring
  rw [hrhs] at hb
  exact (mul_le_mul_iff_right₀ (mul_pos hC (pow_pos hq _))).mp hb

end
end IsingBulk.AnisoF002.RegularTail.C03
