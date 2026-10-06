import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Appendix C, lem:schur, rc4 commit 1b4b506c9cb19d5fdbf9f59d89c7a179739d337d.
The general definitions below implement first-row expansion. The four-variable
identities are symbolic tests only; they do not close the manuscript lemma.
-/

namespace IsingBulk
namespace Schur

variable {R : Type*}

/-- Product over positions i < j, in the order of the input list. -/
def pairProduct [CommRing R] (f : R → R → R) : List R → R
  | [] => 1
  | a :: xs => (xs.map (f a)).prod * pairProduct f xs

/-- First-row Pfaffian expansion with n pairs. Its intended domain is lists
of length 2*n; the empty Pfaffian is one. No division is used in this API. -/
def pfaffian [CommRing R] (A : R → R → R) : ℕ → List R → R
  | 0, _ => 1
  | _ + 1, [] => 0
  | n + 1, a :: xs => (xs.zipIdx.map fun (b, j) =>
      (-1 : R)^j * A a b * pfaffian A n (xs.eraseIdx j)).sum

/-- Numerator obtained by clearing all pair denominators in the expansion.
For length 2*n this is a polynomial expression over any commutative ring. -/
def clearedPfaffian [CommRing R] : ℕ → List R → R
  | 0, _ => 1
  | _ + 1, [] => 0
  | n + 1, a :: xs => (xs.zipIdx.map fun (b, j) =>
      (-1 : R)^j * (a-b) *
      ((xs.eraseIdx j).map (fun c => (1-a*c)*(1-b*c))).prod *
      clearedPfaffian n (xs.eraseIdx j)).sum

/-- A stronger universal polynomial recurrence. This specification remains unproved
and unused by the completed rational-function proof in `SchurMobius`. -/
def SchurRecurrence (R : Type*) [CommRing R] : Prop :=
  ∀ (n : ℕ) (a : R) (xs : List R), xs.length = 2*n+1 →
    pairProduct (fun x y => x-y) (a :: xs) =
      (xs.zipIdx.map fun (b, j) => (-1 : R)^j * (a-b) *
        ((xs.eraseIdx j).map (fun c => (1-a*c)*(1-b*c))).prod *
        pairProduct (fun x y => x-y) (xs.eraseIdx j)).sum

/-- All sizes reduce to the displayed polynomial recurrence. This theorem
has an explicit, unproved recurrence hypothesis; it is not lem:schur. -/
theorem cleared_eq_of_recurrence [CommRing R] (hrec : SchurRecurrence R)
    (n : ℕ) (xs : List R) (hlen : xs.length = 2*n) :
    clearedPfaffian n xs = pairProduct (fun x y => x-y) xs := by
  induction n generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst xs
    rfl
  | succ n ih =>
    cases xs with
    | nil => simp at hlen
    | cons a xs =>
      have hx : xs.length = 2*n+1 := by simp only [List.length_cons] at hlen; omega
      rw [clearedPfaffian, hrec n a xs hx]
      congr 1
      apply List.map_congr_left
      intro bj hbj
      obtain ⟨b,j⟩ := bj
      have hj : j < xs.length := (List.mem_zipIdx' hbj).1
      dsimp only
      rw [ih _ (by rw [List.length_eraseIdx_of_lt hj, hx]; omega)]

theorem cleared_two [CommRing R] (a b : R) :
    clearedPfaffian 1 [a,b] = a-b := by
  simp [clearedPfaffian]

theorem cleared_four [CommRing R] (a b c d : R) :
    clearedPfaffian 2 [a,b,c,d] =
      pairProduct (fun x y => x-y) [a,b,c,d] := by
  simp [clearedPfaffian, pairProduct]
  ring

theorem fraction_four [Field R] (a b c d : R)
    (hab : 1-a*b ≠ 0) (hac : 1-a*c ≠ 0) (had : 1-a*d ≠ 0)
    (hbc : 1-b*c ≠ 0) (hbd : 1-b*d ≠ 0) (hcd : 1-c*d ≠ 0) :
    pfaffian (fun x y => (x-y)/(1-x*y)) 2 [a,b,c,d] =
      pairProduct (fun x y => (x-y)/(1-x*y)) [a,b,c,d] := by
  simp [pfaffian, pairProduct]
  field_simp
  ring

/-- Strict subdisks supply the denominator hypothesis used in Appendix C. -/
theorem denominator_ne_zero {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    1-a*b ≠ 0 := by
  have h : ‖a*b‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg a, norm_nonneg b, mul_nonneg (sub_nonneg.mpr ha.le) (sub_nonneg.mpr hb.le)]
  intro hz
  have hab : a*b = 1 := (sub_eq_zero.mp hz).symm
  simp [hab] at h

/-- The uniform subdisk bounds on y and z in Appendix C imply all pair
denominators are nonzero, for any number of variables. -/
theorem subdisk_denominators {ι : Type*} (v : ι → ℂ) {r : ℝ}
    (hr : r < 1) (hv : ∀ i, ‖v i‖ ≤ r) (i j : ι) :
    1-v i*v j ≠ 0 :=
  denominator_ne_zero ((hv i).trans_lt hr) ((hv j).trans_lt hr)

/-- Regression witness for the semantic warning: a universal pointwise
statement with totalized division would be false. This is not a Schur proof. -/
theorem totalized_division_counterexample :
    pfaffian (fun x y : ℚ => (x-y)/(1-x*y)) 2 [2,1/2,3,4] ≠
      pairProduct (fun x y : ℚ => (x-y)/(1-x*y)) [2,1/2,3,4] := by
  norm_num [pfaffian, pairProduct]

end Schur
end IsingBulk
