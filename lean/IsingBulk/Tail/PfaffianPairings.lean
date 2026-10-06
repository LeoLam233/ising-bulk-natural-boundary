import IsingBulk.Tail.UltraHighMatchings
import Mathlib.Data.List.Perm.Basic

/-! Exact all-order matching enumeration for the frozen Pfaffian recursion.
The enumeration uses coordinate labels, so its terms can be integrated by
measure-preserving pair reindexing without assuming independence. -/
namespace IsingBulk.Tail
noncomputable section

variable {α : Type*}

def perfectPairings : ℕ → List α → List (List (α × α))
  | 0, _ => [[]]
  | _+1, [] => []
  | n+1, a::xs => xs.zipIdx.flatMap (fun bj =>
      (perfectPairings n (xs.eraseIdx bj.2)).map (fun M => (a,bj.1)::M))

def pairingLabels (M : List (α × α)) : List α := M.flatMap (fun p => [p.1,p.2])

def pairingWeight (w : α → α → ℝ) (M : List (α × α)) : ℝ :=
  (M.map (fun p => w p.1 p.2)).prod

def pairingMajorant (w : α → α → ℝ) (n : ℕ) (xs : List α) : ℝ :=
  ((perfectPairings n xs).map (pairingWeight w)).sum

def labelPfaffian (A : α → α → ℂ) : ℕ → List α → ℂ
  | 0, _ => 1
  | _+1, [] => 0
  | n+1, a::xs => (xs.zipIdx.map (fun bj =>
      (-1:ℂ)^bj.2*A a bj.1*labelPfaffian A n (xs.eraseIdx bj.2))).sum

theorem labelPfaffian_source (A : ℂ → ℂ → ℂ) (v : α → ℂ) (n : ℕ) (xs : List α) :
    labelPfaffian (fun a b => A (v a) (v b)) n xs =
      IsingBulk.Schur.pfaffian A n (xs.map v) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      simp only [labelPfaffian,List.map_cons,IsingBulk.Schur.pfaffian,List.zipIdx_map,
        List.map_map,Function.comp_def,List.eraseIdx_map,Prod.map_fst,Prod.map_snd,id_eq,ih]

theorem perfectPairings_length_of_mem (n : ℕ) (xs : List α) (M : List (α × α))
    (hM : M ∈ perfectPairings n xs) : M.length=n := by
  induction n generalizing xs M with
  | zero =>
    have he : M=[] := by simpa only [perfectPairings,List.mem_singleton] using hM
    simp only [he,List.length_nil]
  | succ n ih =>
    cases xs with
    | nil => simp [perfectPairings] at hM
    | cons a xs =>
      obtain ⟨bj,hbj,hM''⟩ := List.mem_flatMap.mp hM
      obtain ⟨M',hM',rfl⟩ := List.mem_map.mp hM''
      simp only [List.length_cons,ih _ _ hM']

theorem pairingWeight_nonneg (w : α → α → ℝ) (hw : ∀ a b, 0 ≤ w a b)
    (M : List (α × α)) : 0 ≤ pairingWeight w M := by
  apply List.prod_nonneg
  intro x hx
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
  exact hw p.1 p.2

theorem pairingMajorant_nonneg (w : α → α → ℝ) (hw : ∀ a b, 0 ≤ w a b)
    (n : ℕ) (xs : List α) : 0 ≤ pairingMajorant w n xs := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨M,hM,rfl⟩ := List.mem_map.mp hx
  exact pairingWeight_nonneg w hw M

theorem sum_flatMap_map {β : Type*} (xs : List α) (f : α → List β) (w : β → ℝ) :
    ((xs.flatMap f).map w).sum = (xs.map (fun a => ((f a).map w).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

theorem pairingMajorant_cons (w : α → α → ℝ) (n : ℕ) (a : α) (xs : List α) :
    pairingMajorant w (n+1) (a::xs) =
      (xs.zipIdx.map (fun bj => w a bj.1*pairingMajorant w n (xs.eraseIdx bj.2))).sum := by
  rw [pairingMajorant,perfectPairings,sum_flatMap_map]
  congr 1
  apply List.map_congr_left
  intro bj hbj
  simp only [List.map_map,Function.comp_def,pairingWeight,List.map_cons,List.prod_cons]
  exact List.sum_map_mul_left _ _ _

theorem list_norm_sum_le_sum_norm (xs : List ℂ) : ‖xs.sum‖ ≤ (xs.map norm).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons,List.map_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

theorem labelPfaffian_norm_le_pairings (A : α → α → ℂ) (w : α → α → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (hA : ∀ a b, ‖A a b‖ ≤ w a b)
    (n : ℕ) (xs : List α) : ‖labelPfaffian A n xs‖ ≤ pairingMajorant w n xs := by
  induction n generalizing xs with
  | zero => simp [labelPfaffian,pairingMajorant,perfectPairings,pairingWeight]
  | succ n ih =>
    cases xs with
    | nil => simp [labelPfaffian,pairingMajorant,perfectPairings]
    | cons a xs =>
      rw [labelPfaffian,pairingMajorant_cons]
      apply (list_norm_sum_le_sum_norm _).trans
      rw [List.map_map]
      apply List.sum_le_sum
      intro bj hbj
      simp only [Function.comp_def,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
      exact mul_le_mul (hA a bj.1) (ih _) (norm_nonneg _) (hw a bj.1)

theorem perfectPairings_labels_perm (n : ℕ) (xs : List α) (hlen : xs.length=2*n)
    (M : List (α × α)) (hM : M ∈ perfectPairings n xs) : List.Perm (pairingLabels M) xs := by
  induction n generalizing xs M with
  | zero =>
    have he : M=[] := by simpa only [perfectPairings,List.mem_singleton] using hM
    have hx : xs=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
    simp only [he,hx,pairingLabels,List.flatMap_nil]
    exact List.Perm.refl []
  | succ n ih =>
    cases xs with
    | nil => simp [perfectPairings] at hM
    | cons a xs =>
      obtain ⟨bj,hbj,hM''⟩ := List.mem_flatMap.mp hM
      obtain ⟨M',hM',rfl⟩ := List.mem_map.mp hM''
      have hj := (List.mem_zipIdx' hbj).1
      have hget := (List.mem_zipIdx' hbj).2
      have hlen' : (xs.eraseIdx bj.2).length=2*n := by
        rw [List.length_eraseIdx_of_lt hj]
        simp only [List.length_cons] at hlen
        omega
      have hp := List.Perm.cons bj.1 (ih _ hlen' M' hM')
      have hp' : List.Perm (bj.1::xs.eraseIdx bj.2) xs := by
        rw [hget]
        exact List.getElem_cons_eraseIdx_perm hj
      simpa only [pairingLabels,List.flatMap_cons,List.append_assoc,List.cons_append,List.nil_append]
        using List.Perm.cons a (hp.trans hp')

theorem list_sum_constant_nat (xs : List α) (k : ℕ) :
    (xs.map (fun _ => k)).sum=xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; ring

theorem perfectPairings_card (n : ℕ) (xs : List α) (hlen : xs.length=2*n) :
    (perfectPairings n xs).length=matchingCount n := by
  induction n generalizing xs with
  | zero => simp [perfectPairings,matchingCount]
  | succ n ih =>
    cases xs with
    | nil => simp at hlen
    | cons a xs =>
      rw [perfectPairings,List.length_flatMap]
      have hsum : (xs.zipIdx.map (fun bj =>
          ((perfectPairings n (xs.eraseIdx bj.2)).map (fun M => (a,bj.1)::M)).length)).sum =
          (xs.zipIdx.map (fun _ => matchingCount n)).sum := by
        congr 1
        apply List.map_congr_left
        intro bj hbj
        rw [List.length_map,ih]
        rw [List.length_eraseIdx_of_lt (List.mem_zipIdx' hbj).1]
        simp only [List.length_cons] at hlen
        omega
      rw [hsum,list_sum_constant_nat,List.length_zipIdx,matchingCount]
      congr 1
      simp only [List.length_cons] at hlen
      omega

end
end IsingBulk.Tail
