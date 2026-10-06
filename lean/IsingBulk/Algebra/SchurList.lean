import IsingBulk.Algebra.SchurInterpolation
import Mathlib.Data.List.InsertIdx
import Mathlib.Data.List.Perm.Basic

/-! Signed deletion identities for the first-row Pfaffian recurrence. -/
namespace IsingBulk.Schur
noncomputable section

theorem map_prod_eraseIdx {R A : Type*} [CommRing R] (f : A → R)
    (xs : List A) (j : ℕ) (hj : j < xs.length) :
    (xs.map f).prod = f xs[j] * ((xs.eraseIdx j).map f).prod := by
  have h := List.CommMonoid.mul_prod_eraseIdx (l := xs.map f) (i := j) (by simpa using hj)
  simpa only [List.getElem_map, List.eraseIdx_map] using h.symm

theorem pairProduct_eraseIdx {R : Type*} [CommRing R] (f : R → R → R)
    (hf : ∀ a b, f a b = -f b a) (xs : List R) (j : ℕ) (hj : j < xs.length) :
    pairProduct f xs = (-1 : R)^j * ((xs.eraseIdx j).map (f xs[j])).prod *
      pairProduct f (xs.eraseIdx j) := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons a xs ih =>
    cases j with
    | zero => simp [pairProduct]
    | succ j =>
      have hj' : j < xs.length := by simpa using hj
      simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ, List.map_cons, List.prod_cons,
        pairProduct, pow_succ]
      rw [map_prod_eraseIdx (f a) xs j hj', ih j hj', hf a xs[j]]
      ring

theorem eraseIdx_toFinset {R : Type*} [DecidableEq R] (xs : List R) (hn : xs.Nodup)
    (j : ℕ) (hj : j < xs.length) :
    (xs.eraseIdx j).toFinset = xs.toFinset.erase xs[j] := by
  rw [← hn.erase_getElem j hj]
  ext x
  simp [hn.mem_erase_iff]

def xKernel {F : Type*} [Field F] (a b : F) : F := (a-b)/(a+b)

theorem xKernel_skew {F : Type*} [Field F] (a b : F) : xKernel a b = -xKernel b a := by
  unfold xKernel
  rw [add_comm b a, ← neg_div, neg_sub]

theorem pairProduct_weight {F : Type*} [Field F] [DecidableEq F]
    (xs : List F) (hn : xs.Nodup) (hs : ∀ b ∈ xs, ∀ c ∈ xs, b ≠ c → b+c ≠ 0)
    (j : ℕ) (hj : j < xs.length) :
    pairProduct xKernel xs * schurWeight xs.toFinset id xs[j] =
      (-1 : F)^j * pairProduct xKernel (xs.eraseIdx j) := by
  have hc : ((xs.eraseIdx j).map (xKernel xs[j])).prod * schurWeight xs.toFinset id xs[j] = 1 := by
    rw [schurWeight, ← eraseIdx_toFinset xs hn j hj,
      List.prod_toFinset _ (hn.eraseIdx j)]
    rw [← List.prod_map_mul]
    apply List.prod_eq_one
    intro v hv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
    have hc' : c ≠ xs[j] ∧ c ∈ xs := by
      rw [← hn.erase_getElem j hj] at hc
      exact hn.mem_erase_iff.mp hc
    dsimp [xKernel]
    have hd := hs xs[j] (List.getElem_mem hj) c hc'.2 hc'.1.symm
    field_simp [hd, sub_ne_zero.mpr hc'.1.symm]
  rw [pairProduct_eraseIdx xKernel xKernel_skew xs j hj]
  calc
    _ = (-1 : F)^j * (((xs.eraseIdx j).map (xKernel xs[j])).prod *
        schurWeight xs.toFinset id xs[j]) * pairProduct xKernel (xs.eraseIdx j) := by ring
    _ = _ := by rw [hc]; ring

theorem xKernel_recurrence {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (a : F) (xs : List F) (hn : xs.Nodup) (h0 : ∀ b ∈ xs, b ≠ 0)
    (hs : ∀ b ∈ xs, ∀ c ∈ xs, b ≠ c → b+c ≠ 0)
    (ha : ∀ b ∈ xs, a+b ≠ 0) (ho : Odd xs.length) :
    pairProduct xKernel (a::xs) =
      (xs.zipIdx.map fun (b,j) => (-1 : F)^j * xKernel a b *
        pairProduct xKernel (xs.eraseIdx j)).sum := by
  have hw := schur_weighted_identity xs.toFinset id (fun _ _ _ _ h => h)
    (by simpa using h0) (by simpa [List.toFinset_card_of_nodup hn] using ho)
    a (by simpa using ha)
  have hm : (xs.zipIdx.map fun (b,j) => (-1 : F)^j * xKernel a b *
      pairProduct xKernel (xs.eraseIdx j)) =
      xs.map (fun b => xKernel a b * schurWeight xs.toFinset id b * pairProduct xKernel xs) := by
    calc
      _ = xs.zipIdx.map (fun bj => xKernel a bj.1 * schurWeight xs.toFinset id bj.1 *
          pairProduct xKernel xs) := by
        apply List.map_congr_left
        rintro ⟨b,j⟩ hbj
        have hj := (List.mem_zipIdx' hbj).1
        have hb := (List.mem_zipIdx' hbj).2
        dsimp only
        rw [hb]
        have h := pairProduct_weight xs hn hs j hj
        linear_combination -(xKernel a xs[j]) * h
      _ = _ := by
        simpa only [List.map_map, Function.comp_def] using
          congrArg (List.map (fun b => xKernel a b * schurWeight xs.toFinset id b * pairProduct xKernel xs))
            (List.zipIdx_map_fst 0 xs)
  rw [hm, pairProduct, ← List.prod_toFinset _ hn, ← List.sum_toFinset _ hn]
  change (∏ b ∈ xs.toFinset, (a-b)/(a+b)) * pairProduct xKernel xs = _
  simp only [id_eq] at hw
  rw [hw, Finset.sum_mul]
  rfl

/-- General even-size identity at distinct nonzero x-values away from pair poles. -/
theorem pfaffian_xKernel_of_nodup {F : Type*} [Field F] [CharZero F]
    (n : ℕ) (xs : List F) (hlen : xs.length = 2*n) (hn : xs.Nodup)
    (h0 : ∀ b ∈ xs, b ≠ 0)
    (hs : ∀ b ∈ xs, ∀ c ∈ xs, b ≠ c → b+c ≠ 0) :
    pfaffian xKernel n xs = pairProduct xKernel xs := by
  classical
  induction n generalizing xs with
  | zero =>
    have he : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst xs
    rfl
  | succ n ih =>
    cases xs with
    | nil => simp at hlen
    | cons a xs =>
      have htail := List.nodup_cons.mp hn
      have hl : xs.length = 2*n+1 := by simp only [List.length_cons] at hlen; omega
      have hs' : ∀ b ∈ xs, ∀ c ∈ xs, b ≠ c → b+c ≠ 0 := by
        intro b hb c hc hbc
        exact hs b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc) hbc
      rw [pfaffian, xKernel_recurrence a xs htail.2
        (fun b hb => h0 b (List.mem_cons_of_mem a hb)) hs'
        (fun b hb => hs a (List.mem_cons_self ..) b (List.mem_cons_of_mem a hb)
          (fun he => htail.1 (he ▸ hb))) (by rw [hl]; exact ⟨n, by omega⟩)]
      congr 1
      apply List.map_congr_left
      rintro ⟨b,j⟩ hbj
      have hj := (List.mem_zipIdx' hbj).1
      dsimp only
      rw [ih _ (by rw [List.length_eraseIdx_of_lt hj, hl]; omega) (htail.2.eraseIdx j)
        (fun c hc => h0 c (List.mem_cons_of_mem a (List.mem_of_mem_eraseIdx hc)))
        (fun c hc d hd hcd => hs' c (List.mem_of_mem_eraseIdx hc) d (List.mem_of_mem_eraseIdx hd) hcd)]

end
end IsingBulk.Schur
