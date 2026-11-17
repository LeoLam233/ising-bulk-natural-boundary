import IsingBulk.AnisoF002.C03.RegularMatching
import IsingBulk.AnisoF002.RegularTail.SchurContraction
import IsingBulk.HT.First.OddSchur

/-!
# Actual even and odd Schur specialization of the new matched bounds

Only the explicitly inspected generic scalar Schur identities are reused.
Their complete elaborated type/value support is recorded separately by
`AuditGenericSchur.lean`.  No historical physical estimate, FIRST, tail,
negative normal form, or natural-boundary result enters these proofs.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
variable {α : Type*}

theorem schur_skew (a b : ℂ) : schur a b = -schur b a := by
  unfold schur
  rw [mul_comm b a, ← neg_div, neg_sub]

theorem pairProductOn_schur (y : α → ℂ) (xs : List α) :
    pairProductOn (fun a b => schur (y a) (y b)) xs =
      IsingBulk.Schur.pairProduct schur (xs.map y) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [pairProductOn, List.map_cons, IsingBulk.Schur.pairProduct,
        List.map_map, Function.comp_def, ih]

theorem pfaffianOn_schur (y : α → ℂ) (n : ℕ) (xs : List α) :
    pfaffianOn (fun a b => schur (y a) (y b)) n xs =
      IsingBulk.Schur.pfaffian schur n (xs.map y) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
      cases xs with
      | nil => rfl
      | cons a xs =>
          simp only [pfaffianOn, List.map_cons, IsingBulk.Schur.pfaffian,
            List.zipIdx_map, List.map_map, Function.comp_def, List.eraseIdx_map,
            Prod.map_fst, Prod.map_snd, id_eq, ih]

theorem schur_even_pfaffianOn (y : α → ℂ) (n : ℕ) (xs : List α)
    (hlen : xs.length = 2 * n) (hd : ∀ a b, 1 - y a * y b ≠ 0) :
    pfaffianOn (fun a b => schur (y a) (y b)) n xs =
      pairProductOn (fun a b => schur (y a) (y b)) xs := by
  rw [pfaffianOn_schur, pairProductOn_schur]
  apply IsingBulk.HT.First.schur_even_list n (xs.map y) (by simpa using hlen)
  intro a ha b hb
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
  exact hd i j

theorem schur_odd_pfaffianOn (y : α → ℂ) (n : ℕ) (xs : List α)
    (hlen : xs.length = 2 * n + 1) (hd : ∀ a b, 1 - y a * y b ≠ 0)
    (hg : ∀ a, y a ≠ -1) :
    pfaffianOn (ghostKernel (fun a b => schur (y a) (y b)) 1)
      (n + 1) (xs.map some ++ [none]) =
        pairProductOn (fun a b => schur (y a) (y b)) xs := by
  let yg : Option α → ℂ := fun a => match a with
    | some a => y a
    | none => -1
  have he : ghostKernel (fun a b => schur (y a) (y b)) 1 =
      fun a b => schur (yg a) (yg b) := by
    funext a b
    cases a <;> cases b
    · simp [ghostKernel, yg, schur]
    · change -(1 : ℂ) = schur (-1) (y _)
      rw [schur_skew (-1)]
      exact congrArg Neg.neg (IsingBulk.HT.First.schur_ghost_entry (hg _)).symm
    · exact (IsingBulk.HT.First.schur_ghost_entry (hg _)).symm
    · rfl
  rw [he, pfaffianOn_schur, pairProductOn_schur]
  have hm : (xs.map some ++ [none]).map yg = xs.map y ++ [-1] := by
    simp [List.map_map, Function.comp_def, yg]
  rw [hm]
  apply IsingBulk.HT.First.schur_odd_specialization n (xs.map y) (by simpa using hlen)
  · intro a ha b hb
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
    exact hd i j
  · intro a ha
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
    exact hg i

theorem schur_pair_product_even_bound (r y : α → ℂ)
    {q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hroot : ∀ a b, ‖schur (r a) (r b)‖ ≤ q)
    (hpair : ∀ a b, ‖schur (r a) (r b) * schur (y a) (y b)‖ ≤ C)
    (hd : ∀ a b, 1 - y a * y b ≠ 0)
    (n : ℕ) (xs : List α) (hlen : xs.length = 2 * n) :
    ‖pairProductOn (fun a b => schur (r a) (r b) * schur (y a) (y b)) xs‖ ≤
      (matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)) := by
  exact paired_product_even_norm_le _ _ (fun a b => schur_skew _ _)
    hq hC hroot hpair n xs hlen (schur_even_pfaffianOn y n xs hlen hd)

theorem schur_pair_product_odd_bound (r y : α → ℂ)
    {q C : ℝ} (hq : 0 < q) (hC : 0 < C)
    (hroot : ∀ a b, ‖schur (r a) (r b)‖ ≤ q)
    (hpair : ∀ a b, ‖schur (r a) (r b) * schur (y a) (y b)‖ ≤ C)
    (hd : ∀ a b, 1 - y a * y b ≠ 0) (hg : ∀ a, y a ≠ -1)
    (n : ℕ) (xs : List α) (hlen : xs.length = 2 * n + 1) :
    ‖pairProductOn (fun a b => schur (r a) (r b) * schur (y a) (y b)) xs‖ ≤
      (matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n) := by
  exact paired_product_odd_norm_le _ _ (fun a b => schur_skew _ _)
    hq hC hroot hpair n xs hlen (schur_odd_pfaffianOn y n xs hlen hd hg)

end
end IsingBulk.AnisoF002.RegularTail.C03
