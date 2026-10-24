import IsingBulk.Anisotropic.Algebra.SkewBlock

namespace IsingBulk.Anisotropic.Algebra
noncomputable section
open scoped BigOperators

/-- Ordered paired coordinates used only for determinant induction. -/
@[reducible] def PairIndex : ℕ → Type
  | 0 => PEmpty
  | n+1 => Fin 2 ⊕ PairIndex n

@[reducible] instance pairIndexFintype : (n : ℕ) → Fintype (PairIndex n)
  | 0 => inferInstanceAs (Fintype PEmpty)
  | n+1 => let _ := pairIndexFintype n; inferInstanceAs (Fintype (Fin 2 ⊕ PairIndex n))

@[reducible] instance pairIndexDecidableEq : (n : ℕ) → DecidableEq (PairIndex n)
  | 0 => inferInstanceAs (DecidableEq PEmpty)
  | n+1 => let _ := pairIndexDecidableEq n; inferInstanceAs (DecidableEq (Fin 2 ⊕ PairIndex n))

def pairedList : {n : ℕ} → (PairIndex n → ℂ) → List ℂ
  | 0, _ => []
  | n+1, v => v (.inl 0) :: v (.inl 1) :: pairedList (fun i : PairIndex n => v (.inr i))

theorem pairedList_prod {n : ℕ} (v : PairIndex n → ℂ) (f : ℂ → ℂ) :
    ((pairedList v).map f).prod = ∏ i, f (v i) := by
  induction n with
  | zero => simp [pairedList, PairIndex]
  | succ n ih =>
    simp only [pairedList,List.map_cons,List.prod_cons,ih]
    rw [Fintype.prod_sum_type]
    simp [Fin.prod_univ_two]
    ring

theorem schurMatrix_sum_eq_blocks {n : ℕ} (v : PairIndex (n+1) → ℂ) :
    schurMatrix v = Matrix.fromBlocks
      (skewPivot (schurKernel (v (.inl 0)) (v (.inl 1))))
      (schurTop (v (.inl 0)) (v (.inl 1)) (fun i => v (.inr i)))
      (schurBottom (v (.inl 0)) (v (.inl 1)) (fun i => v (.inr i)))
      (schurMatrix (fun i => v (.inr i))) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;>
      simp [schurMatrix,skewPivot,schurKernel_self,Matrix.fromBlocks]
    exact schurKernel_swap _ _
  · fin_cases i <;> simp [schurMatrix,schurTop,Matrix.fromBlocks]
  · fin_cases j <;> simp only [schurMatrix,schurBottom,Matrix.fromBlocks_apply₂₁]
    all_goals simpa using schurKernel_swap (v (.inl _)) (v (.inr i))
  · rfl

theorem even_schur_det_of_injective {n : ℕ} (v : PairIndex n → ℂ)
    (hi : Function.Injective v) (hd : ∀ i j, 1-v i*v j ≠ 0) :
    (schurMatrix v).det = (IsingBulk.Schur.pairProduct schurKernel (pairedList v))^2 := by
  induction n with
  | zero => simp [PairIndex,pairedList,IsingBulk.Schur.pairProduct,Matrix.det_isEmpty]
  | succ n ih =>
    have hab : v (.inl 0) ≠ v (.inl 1) := by
      intro he
      have hh := hi he
      have : (0:Fin 2)=1 := Sum.inl.inj hh
      exact (by decide : (0:Fin 2) ≠ 1) this
    rw [schurMatrix_sum_eq_blocks,
      det_schur_block _ _ (fun i : PairIndex n => v (.inr i)) hab (hd _ _)
        (fun i => hd (.inl 0) (.inr i)) (fun i => hd (.inl 1) (.inr i))
        (fun i j => hd (.inr i) (.inr j))]
    rw [ih (fun i => v (.inr i)) (fun _ _ he => Sum.inr.inj (hi he)) (fun _ _ => hd _ _)]
    simp only [pairedList,IsingBulk.Schur.pairProduct,List.map_cons,List.prod_cons,
      pairedList_prod,Finset.prod_mul_distrib]
    ring

end
end IsingBulk.Anisotropic.Algebra
