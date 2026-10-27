import IsingBulk.Preferred22.CoefficientTerms

/-! Polynomial counting of the actual scalar differential-polynomial
terms. Derivative order is fixed before particle count. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators

theorem preferredTermDerivative_length {N : ℕ} (a : Option (Fin N))
    (T : PreferredCoefficientTerm N) : (preferredTermDerivative a T).length=T.length := by
  induction T with
  | nil => rfl
  | cons x xs ih => simp [preferredTermDerivative,ih]

theorem list_flatMap_length_bound {α β : Type*} (L : List α) (F : α → List β)
    (b : ℕ) (h : ∀ x∈L, (F x).length≤b) : (L.flatMap F).length≤L.length*b := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

theorem list_flatMap_length_eq {α β : Type*} (L : List α) (F : α → List β)
    (b : ℕ) (h : ∀ x∈L, (F x).length=b) : (L.flatMap F).length=L.length*b := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,hx,ht]
    ring

theorem preferredTermTransport_length {N : ℕ} (T : PreferredCoefficientTerm N) :
    (preferredTermTransport T).length=(N+1)*T.length+N := by
  unfold preferredTermTransport
  rw [List.length_append,List.length_append,preferredTermDerivative_length,List.length_map]
  rw [list_flatMap_length_eq _ _ T.length (by intro a _; simp [preferredTermDerivative_length])]
  simp only [Finset.length_toList,Finset.card_univ,Fintype.card_fin]
  ring

theorem preferredTermMark_length {N : ℕ} (ij : Fin N × Fin N) (T : PreferredCoefficientTerm N) :
    (preferredTermMark ij T).length=N+1 := by
  simp [preferredTermMark]

def preferredCoefficientCountConstant : ℕ → ℕ
  | 0 => 1
  | j+1 => preferredCoefficientCountConstant j*(4*j+4)

theorem preferredCoefficientCountConstant_pos (j : ℕ) : 0<preferredCoefficientCountConstant j := by
  induction j with
  | zero => norm_num [preferredCoefficientCountConstant]
  | succ j ih => exact Nat.mul_pos ih (by omega)

/-- No N-factorial occurs in the coefficient-term count. A fixed-order
constant times N^j bounds every actual marked word's scalar monomials. -/
theorem preferredCoefficientTerms_count {N : ℕ} (hN : 0<N) (j : ℕ)
    (w : PreferredMarkedWord N j) :
    (preferredCoefficientTerms j w).length≤preferredCoefficientCountConstant j*N^j := by
  induction j with
  | zero => simp [preferredCoefficientTerms,preferredCoefficientCountConstant]
  | succ j ih =>
    have hlength (T : PreferredCoefficientTerm N) (hT : T∈preferredCoefficientTerms j (Fin.tail w)) :
        T.length≤2*j+1 := (preferredCoefficientTerms_wellFormed j (Fin.tail w) T hT).length
    have hmul : (preferredCoefficientTerms j (Fin.tail w)).length*((4*j+4)*N)≤
        preferredCoefficientCountConstant (j+1)*N^(j+1) := by
      calc
        _ ≤ (preferredCoefficientCountConstant j*N^j)*((4*j+4)*N) :=
          Nat.mul_le_mul_right _ (ih (Fin.tail w))
        _ = _ := by rw [preferredCoefficientCountConstant,pow_succ]; ring
    cases hw : w 0 with
    | none =>
      simp only [preferredCoefficientTerms,hw]
      apply (list_flatMap_length_bound _ _ ((4*j+4)*N) ?_).trans hmul
      intro T hT
      rw [preferredTermTransport_length]
      have hh := hlength T hT
      have hn : N+1≤2*N := by omega
      calc
        _ ≤ (2*N)*(2*j+1)+N := Nat.add_le_add_right (Nat.mul_le_mul hn hh) N
        _ ≤ _ := by nlinarith
    | some ij =>
      simp only [preferredCoefficientTerms,hw]
      apply (list_flatMap_length_bound _ _ ((4*j+4)*N) ?_).trans hmul
      intro T _
      rw [preferredTermMark_length]
      nlinarith

end
end IsingBulk.Preferred22
