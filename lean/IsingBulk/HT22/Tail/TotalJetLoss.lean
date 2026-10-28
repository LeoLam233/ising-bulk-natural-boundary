import IsingBulk.Preferred22.CoefficientTerms

/-! The F001 fixed-v field pays one scale power for EVERY derivative,
including parameter derivatives. This replaces the old moving-q
coordinate-only loss while retaining the identical product-rule grammar. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators

def totalAtomLoss {N : ℕ} : PreferredCoefficientAtom N → ℕ
  | .collective _ xs => 1+xs.length
  | _ => 0

def totalTermLoss {N : ℕ} (T : PreferredCoefficientTerm N) : ℕ :=
  (T.map totalAtomLoss).sum

theorem totalAtomShift_loss {N : ℕ} (a : Option (Fin N)) (x : PreferredCoefficientAtom N) :
    totalAtomLoss (preferredAtomShift a x)≤totalAtomLoss x+1 := by
  cases x <;> simp [preferredAtomShift,totalAtomLoss]
  omega

theorem totalTermDerivative_properties {N : ℕ} (a : Option (Fin N))
    (T U : PreferredCoefficientTerm N) (hU : U∈preferredTermDerivative a T) :
    U.length=T.length ∧ preferredTermSeedCount U=preferredTermSeedCount T ∧
      totalTermLoss U≤totalTermLoss T+1 ∧
      (∀ j, (∀ x∈T, preferredAtomJetOrder x≤j) → ∀ x∈U, preferredAtomJetOrder x≤j+1) := by
  induction T generalizing U with
  | nil => simp [preferredTermDerivative] at hU
  | cons x xs ih =>
    simp only [preferredTermDerivative,List.mem_cons,List.mem_map] at hU
    rcases hU with rfl | ⟨V,hV,rfl⟩
    · refine ⟨rfl,?_,?_,?_⟩
      · simp only [preferredTermSeedCount,List.map_cons,List.sum_cons,preferredAtomShift_seedCount]
      · simpa only [totalTermLoss,List.map_cons,List.sum_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
          Nat.add_le_add_right (totalAtomShift_loss a x) (totalTermLoss xs)
      · intro j h x' hx'
        rcases List.mem_cons.mp hx' with rfl | hx'
        · rw [preferredAtomShift_order]
          exact Nat.add_le_add_right (h x (List.mem_cons_self ..)) 1
        · exact (h x' (List.mem_cons_of_mem _ hx')).trans (Nat.le_succ _)
    · obtain ⟨hlen,hseed,hloss,horder⟩ := ih V hV
      refine ⟨by simpa using hlen,?_,?_,?_⟩
      · simp only [preferredTermSeedCount,List.map_cons,List.sum_cons] at hseed ⊢
        rw [hseed]
      · simp only [totalTermLoss,List.map_cons,List.sum_cons] at hloss ⊢
        omega
      · intro j h x' hx'
        rcases List.mem_cons.mp hx' with rfl | hx'
        · exact (h _ (List.mem_cons_self ..)).trans (Nat.le_succ _)
        · exact horder j (fun y hy => h y (List.mem_cons_of_mem _ hy)) x' hx'

structure TotalTermWellFormed {N : ℕ} (j h : ℕ) (T : PreferredCoefficientTerm N) : Prop where
  seed : preferredTermSeedCount T=1
  length : T.length≤2*j+1
  order : ∀ x∈T, preferredAtomJetOrder x≤j
  loss : totalTermLoss T≤h

theorem totalTermTransport_wellFormed {N j h : ℕ} (T U : PreferredCoefficientTerm N)
    (hT : TotalTermWellFormed j h T) (hU : U∈preferredTermTransport T) :
    TotalTermWellFormed (j+1) (h+2) U := by
  have hlenT := hT.length
  have hlossT := hT.loss
  simp only [preferredTermTransport,List.mem_append,List.mem_flatMap,List.mem_map] at hU
  rcases hU with (hU | ⟨a,_,V,hV,rfl⟩) | ⟨a,_,rfl⟩
  · obtain ⟨hlen,hseed,hloss,horder⟩ := totalTermDerivative_properties none T U hU
    exact ⟨hseed.trans hT.seed,by omega,horder j hT.order,by omega⟩
  · obtain ⟨hlen,hseed,hloss,horder⟩ := totalTermDerivative_properties (some a) T V hV
    refine ⟨?_,by simp only [List.length_cons]; omega,?_,?_⟩
    · simpa [preferredTermSeedCount,preferredAtomSeedCount] using hseed.trans hT.seed
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [preferredAtomJetOrder]
      · exact horder j hT.order x hx
    · change 1+totalTermLoss V≤h+2
      omega
  · refine ⟨?_,by simp only [List.length_cons]; omega,?_,?_⟩
    · simpa [preferredTermSeedCount,preferredAtomSeedCount] using hT.seed
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [preferredAtomJetOrder]
      · exact (hT.order x hx).trans (Nat.le_succ _)
    · change 2+totalTermLoss T≤h+2
      omega

theorem totalTermMark_wellFormed {N j h : ℕ} (ij : Fin N × Fin N)
    (T U : PreferredCoefficientTerm N) (hT : TotalTermWellFormed j h T)
    (hU : U∈preferredTermMark ij T) : TotalTermWellFormed (j+1) (h+1) U := by
  have hlenT := hT.length
  simp only [preferredTermMark,List.mem_cons,List.mem_map] at hU
  rcases hU with rfl | ⟨a,_,rfl⟩
  · refine ⟨?_,by simp only [List.length_cons]; omega,?_,?_⟩
    · simpa [preferredTermSeedCount,preferredAtomSeedCount] using hT.seed
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [preferredAtomJetOrder]
      · exact (hT.order x hx).trans (Nat.le_succ _)
    · simpa [totalTermLoss,totalAtomLoss] using hT.loss.trans (Nat.le_succ h)
  · refine ⟨?_,by simp only [List.length_cons]; omega,?_,?_⟩
    · simpa [preferredTermSeedCount,preferredAtomSeedCount] using hT.seed
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [preferredAtomJetOrder]
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [preferredAtomJetOrder]
      · exact (hT.order x hx).trans (Nat.le_succ _)
    · simpa [totalTermLoss,totalAtomLoss,preferredCoordinateJetOrder,Nat.add_comm]
        using Nat.add_le_add_right hT.loss 1

/-- Every explicitly generated monomial contains exactly one normalized
seed. Only collective jets contribute to its degree, which is bounded by
the exact manuscript word loss 2j minus the number of marks. -/
theorem totalCoefficientTerms_wellFormed {N : ℕ} (j : ℕ) (w : PreferredMarkedWord N j)
    (T : PreferredCoefficientTerm N) (hT : T∈preferredCoefficientTerms j w) :
    TotalTermWellFormed j (preferredWordLoss j w) T := by
  induction j generalizing T with
  | zero =>
    have he : T=[.seed []] := by simpa [preferredCoefficientTerms] using hT
    subst T
    constructor <;> simp [preferredTermSeedCount,totalTermLoss,preferredAtomSeedCount,
      totalAtomLoss,preferredAtomJetOrder,preferredWordLoss]
  | succ j ih =>
    cases hw : w 0 with
    | none =>
      simp only [preferredCoefficientTerms,hw,List.mem_flatMap] at hT
      obtain ⟨U,hU,hT⟩ := hT
      simpa only [preferredWordLoss,hw] using
        totalTermTransport_wellFormed U T (ih (Fin.tail w) U hU) hT
    | some ij =>
      simp only [preferredCoefficientTerms,hw,List.mem_flatMap] at hT
      obtain ⟨U,hU,hT⟩ := hT
      simpa only [preferredWordLoss,hw] using
        totalTermMark_wellFormed ij U T (ih (Fin.tail w) U hU) hT

end
end IsingBulk.HT22.Tail
