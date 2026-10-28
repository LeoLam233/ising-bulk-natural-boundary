import IsingBulk.HT22.Algebra.BorderJetAlgebra
import IsingBulk.Preferred22.MarkedMinorDifferentiation

/-! # Differentiation adds one actual ordinary mark, never a border mark -/
namespace IsingBulk.HT22.Algebra
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- The zero-border lift is an actual continuous linear map. -/
def ordinaryDirectionCLM (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ →L[ℂ] Matrix (Fin (N+1)) (Fin (N+1)) ℂ where
  toFun := ordinaryDirection
  map_add' A B := by
    ext i j
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp [ordinaryDirection]
  map_smul' c A := by
    ext i j
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp [ordinaryDirection]
  cont := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp only [ordinaryDirection, ghostBorder_zero_zero, ghostBorder_zero_succ,
        ghostBorder_succ_zero, ghostBorder_succ_succ, neg_zero]
    all_goals fun_prop

@[simp] theorem ordinaryDirectionCLM_apply {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) :
    ordinaryDirectionCLM N K = ordinaryDirection K := rfl

theorem ghostBorder_eq_affine {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) :
    ghostBorder K (fun _ => 1) =
      ordinaryDirectionCLM N K + ghostBorder 0 (fun _ => 1) := by
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [ordinaryDirection]

@[simp] theorem ordinaryMarks_cons {N ell : ℕ} (a : Fin N × Fin N)
    (marks : Fin ell → Fin N × Fin N) :
    ordinaryMarks (Fin.cons a marks) = Fin.cons (a.1.succ,a.2.succ) (ordinaryMarks marks) := by
  funext r
  cases r using Fin.cases <;> simp [ordinaryMarks]

/-- The generic marked derivative along an ordinary zero-border direction. -/
theorem markedDeterminant_fderiv_ordinary {N ell : ℕ}
    (K : Matrix (Fin (N+1)) (Fin (N+1)) ℂ) (B : Matrix (Fin N) (Fin N) ℂ)
    (marks : Fin ell → Fin N × Fin N) :
    fderiv ℂ (fun A => markedDeterminant A (ordinaryMarks marks)) K (ordinaryDirection B) =
      ∑ a : Fin N × Fin N, B a.1 a.2 *
        markedDeterminant K (ordinaryMarks (Fin.cons a marks)) := by
  rw [markedDeterminant_fderiv]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, ordinaryDirection,
    ghostBorder_zero_zero, ghostBorder_zero_succ, ghostBorder_succ_zero,
    ghostBorder_succ_succ, zero_mul, neg_zero, Finset.sum_const_zero, zero_add,
    ordinaryMarks_cons]

/-- Complex parameter differentiation of the actual bordered marked minor. -/
theorem borderedMarkedDeterminant_comp_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N ell : ℕ} (K : E → Matrix (Fin N) (Fin N) ℂ) (x v : E)
    (hK : DifferentiableAt ℂ K x) (marks : Fin ell → Fin N × Fin N) :
    fderiv ℂ (fun y => borderedMarkedDeterminant (K y) marks) x v =
      ∑ a : Fin N × Fin N, (fderiv ℂ K x v) a.1 a.2 *
        borderedMarkedDeterminant (K x) (Fin.cons a marks) := by
  let G : E → Matrix (Fin (N+1)) (Fin (N+1)) ℂ := fun y => ghostBorder (K y) (fun _ => 1)
  have heq : G = fun y => ordinaryDirectionCLM N (K y) + ghostBorder 0 (fun _ => 1) := by
    funext y
    exact ghostBorder_eq_affine (K y)
  have hG : HasFDerivAt G ((ordinaryDirectionCLM N).comp (fderiv ℂ K x)) x := by
    rw [heq]
    exact ((ordinaryDirectionCLM N).hasFDerivAt.comp x hK.hasFDerivAt).add_const _
  have hm : DifferentiableAt ℂ (fun A => markedDeterminant A (ordinaryMarks marks)) (G x) :=
    ((markedDeterminant_contDiff _).differentiable (by simp)).differentiableAt
  have hh := hm.hasFDerivAt.comp x hG
  have hv := congrArg (fun L : E →L[ℂ] ℂ => L v) hh.fderiv
  change fderiv ℂ (fun y => borderedMarkedDeterminant (K y) marks) x v = _ at hv
  rw [hv]
  exact markedDeterminant_fderiv_ordinary (G x) (fderiv ℂ K x v) marks

/-- Real angular differentiation needs no holomorphic extension of cutoffs. -/
theorem borderedMarkedDeterminant_comp_real_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N ell : ℕ} (K : E → Matrix (Fin N) (Fin N) ℂ) (x v : E)
    (hK : DifferentiableAt ℝ K x) (marks : Fin ell → Fin N × Fin N) :
    fderiv ℝ (fun y => borderedMarkedDeterminant (K y) marks) x v =
      ∑ a : Fin N × Fin N, (fderiv ℝ K x v) a.1 a.2 *
        borderedMarkedDeterminant (K x) (Fin.cons a marks) := by
  let G : E → Matrix (Fin (N+1)) (Fin (N+1)) ℂ := fun y => ghostBorder (K y) (fun _ => 1)
  have heq : G = fun y => ordinaryDirectionCLM N (K y) + ghostBorder 0 (fun _ => 1) := by
    funext y
    exact ghostBorder_eq_affine (K y)
  have hG : HasFDerivAt G
      (((ordinaryDirectionCLM N).restrictScalars ℝ).comp (fderiv ℝ K x)) x := by
    rw [heq]
    exact (((ordinaryDirectionCLM N).restrictScalars ℝ).hasFDerivAt.comp x hK.hasFDerivAt).add_const _
  have hm : DifferentiableAt ℂ (fun A => markedDeterminant A (ordinaryMarks marks)) (G x) :=
    ((markedDeterminant_contDiff _).differentiable (by simp)).differentiableAt
  have hh := (hm.hasFDerivAt.restrictScalars ℝ).comp x hG
  have hv := congrArg (fun L : E →L[ℝ] ℂ => L v) hh.fderiv
  change fderiv ℝ (fun y => borderedMarkedDeterminant (K y) marks) x v = _ at hv
  rw [hv]
  exact markedDeterminant_fderiv_ordinary (G x) (fderiv ℝ K x v) marks

end
end IsingBulk.HT22.Algebra
