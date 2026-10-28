import IsingBulk.HT22.Algebra.BorderedKernel
import IsingBulk.Preferred22.MarkedMinorBound

/-! # The border-specific marked-minor estimate

Only ordinary entries are marked. Multiplying the ghost column by the entry
scale before row normalization gains exactly two ordinary-block dimensions:
the unmarked scale is `a^(N-1-ell)`, not `a^(N+1-ell)`.
-/
namespace IsingBulk.HT22.Algebra
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- Marks embed only into ordinary entries; neither border is differentiated. -/
def ordinaryMarks {N ell : ℕ} (marks : Fin ell → Fin N × Fin N) :
    Fin ell → Fin (N+1) × Fin (N+1) :=
  fun r => ((marks r).1.succ, (marks r).2.succ)

def borderedMarkedDeterminant {N ell : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (marks : Fin ell → Fin N × Fin N) : ℂ :=
  markedDeterminant (ghostBorder K (fun _ => 1)) (ordinaryMarks marks)

/-- A repeated ordinary marked row vanishes, including on collisions. -/
theorem borderedMarkedDeterminant_row_collision {N ell : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : Fin ell → Fin N × Fin N)
    (r t : Fin ell) (hrt : r ≠ t) (hrow : (marks r).1 = (marks t).1) :
    borderedMarkedDeterminant K marks = 0 := by
  exact markedDeterminant_eq_zero_of_row_collision _ _ r t hrt
    (congrArg Fin.succ hrow)

/-- The exact Hadamard bound before extracting the one ghost-column scale. -/
theorem borderedMarkedDeterminant_scaled_bound {N ell : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : Fin ell → Fin N × Fin N)
    (a : ℝ) (ha : 0 < a) (hK : ∀ i j, ‖K i j‖ ≤ a) :
    a * ‖borderedMarkedDeterminant K marks‖ ≤
      (Real.sqrt (N+1))^(N+1) * a^(N-ell) := by
  classical
  by_cases hrow : Function.Injective (fun r => (marks r).1)
  · let e := markedRowEmbedding marks hrow
    have hrow' : Function.Injective (fun r => (ordinaryMarks marks r).1) := by
      intro r t h
      exact hrow (Fin.succ_injective _ h)
    let e' := markedRowEmbedding (ordinaryMarks marks) hrow'
    let A := replacedRows (ghostBorder K (fun _ => 1))
      (fun r => Matrix.single (ordinaryMarks marks r).1 (ordinaryMarks marks r).2 (1:ℂ)) e'
    let d : Fin (N+1) → ℂ := Fin.cons (a:ℂ) (fun _ => 1)
    let B := A * Matrix.diagonal d
    let w : Fin (N+1) → ℝ := Fin.cons 1 (fun i => if i ∈ Set.range e then 1 else a)
    have hzero : (0 : Fin (N+1)) ∉ Set.range e' := by
      rintro ⟨r, hr⟩
      exact Fin.succ_ne_zero (marks r).1 hr
    have hsucc (i : Fin N) (hi : i ∉ Set.range e) : i.succ ∉ Set.range e' := by
      rintro ⟨r, hr⟩
      exact hi ⟨r, Fin.succ_injective _ hr⟩
    have hw : ∀ i, 0 < w i := by
      intro i
      cases i using Fin.cases
      · simp [w]
      · simp only [w, Fin.cons_succ]
        split_ifs <;> positivity
    have hB : ∀ i j, ‖B i j‖ ≤ w i := by
      intro i j
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases <;>
          simp [B, Matrix.mul_diagonal, A, replacedRows, hzero, d, w]
      | succ i =>
        by_cases hi : i ∈ Set.range e
        · obtain ⟨r, rfl⟩ := hi
          have he : A ((marks r).1.succ) = Pi.single ((marks r).2.succ) 1 :=
            marked_replacedRows_selected _ (ordinaryMarks marks) hrow' r
          change ‖B ((marks r).1.succ) j‖ ≤ _
          simp only [B, Matrix.mul_diagonal, he]
          cases j using Fin.cases with
          | zero => simp [Fin.succ_ne_zero, d, w]
          | succ j =>
            simp only [Pi.single_apply, d, Fin.cons_succ, mul_one]
            split_ifs <;> simp [w, e, markedRowEmbedding]
        · simp only [w, Fin.cons_succ, ite_eq_right hi]
          cases j using Fin.cases
          · simp [B, Matrix.mul_diagonal, A, replacedRows, hsucc i hi, d,
              Complex.norm_real, Real.norm_of_nonneg ha.le]
          · simpa [B, Matrix.mul_diagonal, A, replacedRows, hsucc i hi, d] using hK i _
    have hb := norm_det_sq_le_row_entry_weights (by omega : 0<N+1) B w hw hB
    have hp : (∏ i, w i) = a^(N-ell) := by
      simp only [w, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, one_mul]
      exact product_unmarked_weight e a
    have hd : B.det = A.det*(a:ℂ) := by
      rw [Matrix.det_mul, Matrix.det_diagonal]
      simp [d, Fin.prod_univ_succ]
    have hm : A.det = borderedMarkedDeterminant K marks :=
      (markedDeterminant_eq_row_replacement _ _ hrow').symm
    rw [hp, hd, hm, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le] at hb
    have hs : ((Real.sqrt (N+1))^(N+1)*a^(N-ell))^2 =
        ((N+1):ℝ)^(N+1)*(a^(N-ell))^2 := by
      rw [mul_pow, ←pow_mul, Nat.mul_comm (N+1) 2, pow_mul,
        Real.sq_sqrt (by positivity)]
    simp only [Nat.cast_add, Nat.cast_one] at hb
    rw [←hs] at hb
    have h := (sq_le_sq₀ (by positivity : 0 ≤ ‖borderedMarkedDeterminant K marks‖*a)
      (by positivity)).mp hb
    simpa only [mul_comm a] using h
  · simp only [Function.Injective] at hrow
    push Not at hrow
    obtain ⟨r,t,hrt,hne⟩ := hrow
    rw [borderedMarkedDeterminant_row_collision K marks r t hne hrt]
    simp only [norm_zero, mul_zero]
    positivity

/-- The sharp ordinary-entry exponent from F001 Lemma 4.4. -/
theorem borderedMarkedDeterminant_hadamard {N ell : ℕ}
    (hell : ell ≤ N-1) (hN : 0 < N)
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : Fin ell → Fin N × Fin N)
    (a : ℝ) (ha : 0 < a) (hK : ∀ i j, ‖K i j‖ ≤ a) :
    ‖borderedMarkedDeterminant K marks‖ ≤
      (Real.sqrt (N+1))^(N+1) * a^(N-1-ell) := by
  have h := borderedMarkedDeterminant_scaled_bound K marks a ha hK
  have hexp : N-ell = (N-1-ell)+1 := by omega
  rw [hexp, pow_succ a] at h
  apply (mul_le_mul_iff_left₀ ha).mp
  convert h using 1 <;> ring

end
end IsingBulk.HT22.Algebra
