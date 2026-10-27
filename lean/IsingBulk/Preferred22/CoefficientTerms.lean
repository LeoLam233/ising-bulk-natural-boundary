import IsingBulk.Preferred22.MarkedTransportRecursion

/-! Explicit differential-polynomial terms for the genuine scalar word
coefficients. Only collective-field atoms carry diameter loss. The seed
atom is unique, retaining its exact factorial/Haar normalizer. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators

inductive PreferredCoefficientAtom (N : ℕ) where
  | seed (xs : List (Option (Fin N)))
  | collective (i : Fin N) (xs : List (Option (Fin N)))
  | kernel (a : Fin N × Fin N) (xs : List (Option (Fin N)))
  deriving DecidableEq

def preferredAtomShift {N : ℕ} (a : Option (Fin N)) :
    PreferredCoefficientAtom N → PreferredCoefficientAtom N
  | .seed xs => .seed (a::xs)
  | .collective i xs => .collective i (a::xs)
  | .kernel ij xs => .kernel ij (a::xs)

def preferredAtomJetOrder {N : ℕ} : PreferredCoefficientAtom N → ℕ
  | .seed xs | .collective _ xs | .kernel _ xs => xs.length

def preferredAtomSeedCount {N : ℕ} : PreferredCoefficientAtom N → ℕ
  | .seed _ => 1
  | _ => 0

def preferredAtomLoss {N : ℕ} : PreferredCoefficientAtom N → ℕ
  | .collective _ xs => 1+preferredCoordinateJetOrder xs
  | _ => 0

def preferredAtomValue {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (a : PreferredCoefficientAtom N) : ℂ → (Fin N → ℝ) → ℂ :=
  match a with
  | .seed xs => preferredFrameJet τ p m (preferredRegularSeedCoefficient τ η p m r) xs
  | .collective i xs => preferredFrameJet τ p m
      (fun s θ => preferredResidualCollective s (preferredSourceCoordinate τ p m s θ) i) xs
  | .kernel ij xs => preferredFrameJet τ p m
      (fun s θ => preferredSourceRegularKernel τ p m s θ ij.1 ij.2) xs

abbrev PreferredCoefficientTerm (N : ℕ) := List (PreferredCoefficientAtom N)

def preferredTermLoss {N : ℕ} (T : PreferredCoefficientTerm N) : ℕ :=
  (T.map preferredAtomLoss).sum

def preferredTermSeedCount {N : ℕ} (T : PreferredCoefficientTerm N) : ℕ :=
  (T.map preferredAtomSeedCount).sum

def preferredTermValue {N : ℕ} (τ : ℝ) (η p m r : ℝ → ℝ)
    (T : PreferredCoefficientTerm N) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (T.map (fun a => preferredAtomValue τ η p m r a s θ)).prod

/-- Product-rule terms, preserving the ordered derivative words. -/
def preferredTermDerivative {N : ℕ} (a : Option (Fin N)) :
    PreferredCoefficientTerm N → List (PreferredCoefficientTerm N)
  | [] => []
  | x::xs => (preferredAtomShift a x::xs)::
      ((preferredTermDerivative a xs).map (fun T => x::T))

/-- The actual regular generator consists of E_s, B_a E_a, and div B. -/
def preferredTermTransport {N : ℕ} (T : PreferredCoefficientTerm N) :
    List (PreferredCoefficientTerm N) :=
  preferredTermDerivative none T ++
    ((Finset.univ.toList : List (Fin N)).flatMap (fun a =>
      (preferredTermDerivative (some a) T).map (fun U => .collective a []::U))) ++
    ((Finset.univ.toList : List (Fin N)).map (fun a => .collective a [some a]::T))

/-- A marked entry contributes E_s K plus B_a E_a K, with one loss at most. -/
def preferredTermMark {N : ℕ} (ij : Fin N × Fin N) (T : PreferredCoefficientTerm N) :
    List (PreferredCoefficientTerm N) :=
  (.kernel ij [none]::T)::
    ((Finset.univ.toList : List (Fin N)).map (fun a =>
      .collective a []::.kernel ij [some a]::T))

def preferredCoefficientTerms {N : ℕ} :
    (j : ℕ) → PreferredMarkedWord N j → List (PreferredCoefficientTerm N)
  | 0, _ => [[.seed []]]
  | j+1, w => match w 0 with
    | none => (preferredCoefficientTerms j (Fin.tail w)).flatMap preferredTermTransport
    | some ij => (preferredCoefficientTerms j (Fin.tail w)).flatMap (preferredTermMark ij)

theorem preferredAtomShift_seedCount {N : ℕ} (a : Option (Fin N)) (x : PreferredCoefficientAtom N) :
    preferredAtomSeedCount (preferredAtomShift a x)=preferredAtomSeedCount x := by
  cases x <;> rfl

theorem preferredAtomShift_order {N : ℕ} (a : Option (Fin N)) (x : PreferredCoefficientAtom N) :
    preferredAtomJetOrder (preferredAtomShift a x)=preferredAtomJetOrder x+1 := by
  cases x <;> rfl

theorem preferredAtomShift_loss {N : ℕ} (a : Option (Fin N)) (x : PreferredCoefficientAtom N) :
    preferredAtomLoss (preferredAtomShift a x)≤preferredAtomLoss x+(if a.isSome then 1 else 0) := by
  cases x <;> cases a <;> simp [preferredAtomShift,preferredAtomLoss,preferredCoordinateJetOrder]
  omega

theorem preferredTermDerivative_properties {N : ℕ} (a : Option (Fin N))
    (T U : PreferredCoefficientTerm N) (hU : U∈preferredTermDerivative a T) :
    U.length=T.length ∧ preferredTermSeedCount U=preferredTermSeedCount T ∧
      preferredTermLoss U≤preferredTermLoss T+(if a.isSome then 1 else 0) ∧
      (∀ j, (∀ x∈T, preferredAtomJetOrder x≤j) → ∀ x∈U, preferredAtomJetOrder x≤j+1) := by
  induction T generalizing U with
  | nil => simp [preferredTermDerivative] at hU
  | cons x xs ih =>
    simp only [preferredTermDerivative,List.mem_cons,List.mem_map] at hU
    rcases hU with rfl | ⟨V,hV,rfl⟩
    · refine ⟨rfl,?_,?_,?_⟩
      · simp only [preferredTermSeedCount,List.map_cons,List.sum_cons,preferredAtomShift_seedCount]
      · simpa only [preferredTermLoss,List.map_cons,List.sum_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
          Nat.add_le_add_right (preferredAtomShift_loss a x) (preferredTermLoss xs)
      · intro j h x' hx'
        rcases List.mem_cons.mp hx' with rfl | hx'
        · rw [preferredAtomShift_order]
          exact Nat.add_le_add_right (h x (List.mem_cons_self ..)) 1
        · exact (h x' (List.mem_cons_of_mem _ hx')).trans (Nat.le_succ _)
    · obtain ⟨hlen,hseed,hloss,horder⟩ := ih V hV
      refine ⟨by simpa using hlen,?_,?_,?_⟩
      · simp only [preferredTermSeedCount,List.map_cons,List.sum_cons] at hseed ⊢
        rw [hseed]
      · simp only [preferredTermLoss,List.map_cons,List.sum_cons] at hloss ⊢
        omega
      · intro j h x' hx'
        rcases List.mem_cons.mp hx' with rfl | hx'
        · exact (h _ (List.mem_cons_self ..)).trans (Nat.le_succ _)
        · exact horder j (fun y hy => h y (List.mem_cons_of_mem _ hy)) x' hx'

structure PreferredTermWellFormed {N : ℕ} (j h : ℕ) (T : PreferredCoefficientTerm N) : Prop where
  seed : preferredTermSeedCount T=1
  length : T.length≤2*j+1
  order : ∀ x∈T, preferredAtomJetOrder x≤j
  loss : preferredTermLoss T≤h

theorem preferredTermTransport_wellFormed {N j h : ℕ} (T U : PreferredCoefficientTerm N)
    (hT : PreferredTermWellFormed j h T) (hU : U∈preferredTermTransport T) :
    PreferredTermWellFormed (j+1) (h+2) U := by
  have hlenT := hT.length
  have hlossT := hT.loss
  simp only [preferredTermTransport,List.mem_append,List.mem_flatMap,List.mem_map] at hU
  rcases hU with (hU | ⟨a,_,V,hV,rfl⟩) | ⟨a,_,rfl⟩
  · obtain ⟨hlen,hseed,hloss,horder⟩ := preferredTermDerivative_properties none T U hU
    have hloss' : preferredTermLoss U≤preferredTermLoss T := by simpa using hloss
    exact ⟨hseed.trans hT.seed,by omega,horder j hT.order,by omega⟩
  · obtain ⟨hlen,hseed,hloss,horder⟩ := preferredTermDerivative_properties (some a) T V hV
    refine ⟨?_,by simp only [List.length_cons]; omega,?_,?_⟩
    · simpa [preferredTermSeedCount,preferredAtomSeedCount] using hseed.trans hT.seed
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [preferredAtomJetOrder]
      · exact horder j hT.order x hx
    · change 1+preferredTermLoss V≤h+2
      simp only [Option.isSome_some,ite_true] at hloss
      omega
  · refine ⟨?_,by simp only [List.length_cons]; omega,?_,?_⟩
    · simpa [preferredTermSeedCount,preferredAtomSeedCount] using hT.seed
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [preferredAtomJetOrder]
      · exact (hT.order x hx).trans (Nat.le_succ _)
    · change 2+preferredTermLoss T≤h+2
      omega

theorem preferredTermMark_wellFormed {N j h : ℕ} (ij : Fin N × Fin N)
    (T U : PreferredCoefficientTerm N) (hT : PreferredTermWellFormed j h T)
    (hU : U∈preferredTermMark ij T) : PreferredTermWellFormed (j+1) (h+1) U := by
  have hlenT := hT.length
  simp only [preferredTermMark,List.mem_cons,List.mem_map] at hU
  rcases hU with rfl | ⟨a,_,rfl⟩
  · refine ⟨?_,by simp only [List.length_cons]; omega,?_,?_⟩
    · simpa [preferredTermSeedCount,preferredAtomSeedCount] using hT.seed
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [preferredAtomJetOrder]
      · exact (hT.order x hx).trans (Nat.le_succ _)
    · simpa [preferredTermLoss,preferredAtomLoss] using hT.loss.trans (Nat.le_succ h)
  · refine ⟨?_,by simp only [List.length_cons]; omega,?_,?_⟩
    · simpa [preferredTermSeedCount,preferredAtomSeedCount] using hT.seed
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [preferredAtomJetOrder]
      rcases List.mem_cons.mp hx with rfl | hx
      · simp [preferredAtomJetOrder]
      · exact (hT.order x hx).trans (Nat.le_succ _)
    · simpa [preferredTermLoss,preferredAtomLoss,preferredCoordinateJetOrder,Nat.add_comm]
        using Nat.add_le_add_right hT.loss 1

/-- Every explicitly generated monomial contains exactly one normalized
seed. Only collective jets contribute to its degree, which is bounded by
the exact manuscript word loss 2j minus the number of marks. -/
theorem preferredCoefficientTerms_wellFormed {N : ℕ} (j : ℕ) (w : PreferredMarkedWord N j)
    (T : PreferredCoefficientTerm N) (hT : T∈preferredCoefficientTerms j w) :
    PreferredTermWellFormed j (preferredWordLoss j w) T := by
  induction j generalizing T with
  | zero =>
    have he : T=[.seed []] := by simpa [preferredCoefficientTerms] using hT
    subst T
    constructor <;> simp [preferredTermSeedCount,preferredTermLoss,preferredAtomSeedCount,
      preferredAtomLoss,preferredAtomJetOrder,preferredWordLoss]
  | succ j ih =>
    cases hw : w 0 with
    | none =>
      simp only [preferredCoefficientTerms,hw,List.mem_flatMap] at hT
      obtain ⟨U,hU,hT⟩ := hT
      simpa only [preferredWordLoss,hw] using
        preferredTermTransport_wellFormed U T (ih (Fin.tail w) U hU) hT
    | some ij =>
      simp only [preferredCoefficientTerms,hw,List.mem_flatMap] at hT
      obtain ⟨U,hU,hT⟩ := hT
      simpa only [preferredWordLoss,hw] using
        preferredTermMark_wellFormed ij U T (ih (Fin.tail w) U hU) hT

end
end IsingBulk.Preferred22
