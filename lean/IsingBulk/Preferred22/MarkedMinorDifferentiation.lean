import IsingBulk.Preferred22.MarkedDeterminant

/-! Differentiating a genuine marked minor adds exactly one actual matrix
entry mark. This is the recursive algebra used by the transport filtration,
and remains valid at every collision locus. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem multilinear_matrix_head_expansion {N ell : ℕ}
    (F : (Matrix (Fin N) (Fin N) ℂ) [×ell+1]→L[ℂ] ℂ)
    (B : Matrix (Fin N) (Fin N) ℂ)
    (v : Fin ell → Matrix (Fin N) (Fin N) ℂ) :
    F (Fin.cons B v) = ∑ a : Fin N × Fin N,
      B a.1 a.2 * F (Fin.cons (Matrix.single a.1 a.2 (1:ℂ)) v) := by
  classical
  let L : Matrix (Fin N) (Fin N) ℂ →L[ℂ] ℂ :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin ell => Matrix (Fin N) (Fin N) ℂ) ℂ v).comp
      F.curryLeft
  have hL (A : Matrix (Fin N) (Fin N) ℂ) : L A = F (Fin.cons A v) := by
    simp only [L, ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply,
      ContinuousMultilinearMap.curryLeft_apply]
  conv_lhs => rw [←hL B, matrix_direction_entry_expansion B]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  simp only [hL]

theorem markedDeterminant_contDiff {N ell : ℕ} (marks : Fin ell → Fin N × Fin N) :
    ContDiff ℂ ∞ (fun K : Matrix (Fin N) (Fin N) ℂ => markedDeterminant K marks) := by
  let v : Fin ell → Matrix (Fin N) (Fin N) ℂ :=
    fun r => Matrix.single (marks r).1 (marks r).2 (1:ℂ)
  have h := (determinant_contDiff N).iteratedFDeriv_right (i := ell) (m := ∞) (by simp)
  exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin ell => Matrix (Fin N) (Fin N) ℂ)
    ℂ v).contDiff.comp h

/-- One derivative adds one marked matrix entry, with the actual direction
entry as its coefficient. -/
theorem markedDeterminant_fderiv {N ell : ℕ}
    (K B : Matrix (Fin N) (Fin N) ℂ) (marks : Fin ell → Fin N × Fin N) :
    fderiv ℂ (fun A => markedDeterminant A marks) K B =
      ∑ a : Fin N × Fin N, B a.1 a.2 * markedDeterminant K (Fin.cons a marks) := by
  classical
  let v : Fin ell → Matrix (Fin N) (Fin N) ℂ :=
    fun r => Matrix.single (marks r).1 (marks r).2 (1:ℂ)
  have hf : DifferentiableAt ℂ (iteratedFDeriv ℂ ell
      (Matrix.det : Matrix (Fin N) (Fin N) ℂ → ℂ)) K :=
    (((determinant_contDiff N).iteratedFDeriv_right (i := ell) (m := 1) (by simp)).differentiable
      (by norm_num)).differentiableAt
  have he : fderiv ℂ (fun A => markedDeterminant A marks) K B =
      iteratedFDeriv ℂ (ell+1) Matrix.det K (Fin.cons B v) := by
    simpa only [markedDeterminant, Fin.tail_cons, Fin.cons_zero] using
      (hf.iteratedFDeriv_succ_apply_left' (m := Fin.cons B v)).symm
  rw [he, multilinear_matrix_head_expansion]
  apply Finset.sum_congr rfl
  intro a _
  congr 1

theorem markedDeterminant_comp_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N ell : ℕ} (K : E → Matrix (Fin N) (Fin N) ℂ) (x v : E)
    (hK : DifferentiableAt ℂ K x) (marks : Fin ell → Fin N × Fin N) :
    fderiv ℂ (fun y => markedDeterminant (K y) marks) x v =
      ∑ a : Fin N × Fin N, (fderiv ℂ K x v) a.1 a.2 *
        markedDeterminant (K x) (Fin.cons a marks) := by
  have hm : DifferentiableAt ℂ (fun A : Matrix (Fin N) (Fin N) ℂ =>
      markedDeterminant A marks) (K x) :=
    ((markedDeterminant_contDiff marks).differentiable (by simp)).differentiableAt
  have hh := hm.hasFDerivAt.comp x hK.hasFDerivAt
  calc
    _ = fderiv ℂ (fun A => markedDeterminant A marks) (K x) (fderiv ℂ K x v) := by
      exact congrArg (fun L : E →L[ℂ] ℂ => L v) hh.fderiv
    _ = _ := markedDeterminant_fderiv (K x) (fderiv ℂ K x v) marks

/-- Real angular derivatives act on the same complex marked minors by
restriction of scalars. Smooth real cutoffs need no complex extension. -/
theorem markedDeterminant_comp_real_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N ell : ℕ} (K : E → Matrix (Fin N) (Fin N) ℂ) (x v : E)
    (hK : DifferentiableAt ℝ K x) (marks : Fin ell → Fin N × Fin N) :
    fderiv ℝ (fun y => markedDeterminant (K y) marks) x v =
      ∑ a : Fin N × Fin N, (fderiv ℝ K x v) a.1 a.2 *
        markedDeterminant (K x) (Fin.cons a marks) := by
  have hm : DifferentiableAt ℂ (fun A : Matrix (Fin N) (Fin N) ℂ =>
      markedDeterminant A marks) (K x) :=
    ((markedDeterminant_contDiff marks).differentiable (by simp)).differentiableAt
  have hh := (hm.hasFDerivAt.restrictScalars ℝ).comp x hK.hasFDerivAt
  calc
    _ = fderiv ℂ (fun A => markedDeterminant A marks) (K x) (fderiv ℝ K x v) := by
      exact congrArg (fun L : E →L[ℝ] ℂ => L v) hh.fderiv
    _ = _ := markedDeterminant_fderiv (K x) (fderiv ℝ K x v) marks

end
end IsingBulk.Preferred22
