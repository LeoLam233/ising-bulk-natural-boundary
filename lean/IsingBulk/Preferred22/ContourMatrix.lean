import IsingBulk.Preferred22.Contour
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! The full balanced Jacobian and its exact restriction to the zero-sum
tangent hyperplane. This is finite matrix algebra, with no contour or tail
assumption. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem determinant_restrict_sum_hyperplane {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hA : ∀ j, ∑ i, A i j = 1) :
    A.det = Matrix.det (fun i j : Fin n => A i.castSucc j.castSucc - A i.castSucc (Fin.last n)) := by
  let B := A.updateRow (Fin.last n) (fun _ => 1)
  have hB : B.det=A.det := by
    have he : (∑ i : Fin (n+1), A i)=(fun _ => 1) := by
      funext j
      simpa using hA j
    simpa only [one_smul, he, B] using Matrix.det_updateRow_sum A (Fin.last n) (fun _ => (1:ℂ))
  let u : Fin (n+1) → ℂ := Pi.single (Fin.last n) (-1)
  let v : Fin (n+1) → ℂ := fun j => if j=Fin.last n then 0 else 1
  let T : Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
    1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit v
  have hT : T.det=1 := by
    change (1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit v).det=1
    rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp [dotProduct, u, v, Pi.single_apply]
  have hBT (i j : Fin (n+1)) : (B*T) i j = B i j - B i (Fin.last n)*v j := by
    change (B*(1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit v) :
      Matrix (Fin (n+1)) (Fin (n+1)) ℂ) i j = _
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    simp only [Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, Fintype.sum_unique,
      u, Pi.single_apply, mul_ite, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hlast (j : Fin (n+1)) : (B*T) (Fin.last n) j = if j=Fin.last n then 1 else 0 := by
    rw [hBT]
    by_cases hj : j=Fin.last n <;> simp [B, v, hj]
  have hminor : (B*T).submatrix Fin.castSucc Fin.castSucc =
      (fun i j : Fin n => A i.castSucc j.castSucc - A i.castSucc (Fin.last n)) := by
    ext i j
    rw [Matrix.submatrix_apply, hBT]
    simp [B, v, Fin.castSucc_ne_last, Matrix.updateRow_ne]
  have hdet : (B*T).det =
      Matrix.det (fun i j : Fin n => A i.castSucc j.castSucc - A i.castSucc (Fin.last n)) := by
    rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
    simp [hlast, hminor, Fin.castSucc_ne_last]
  simpa only [Matrix.det_mul, hT, mul_one, hB] using hdet

def fullAngularJacobian {N : ℕ} (τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (if i=j then 1 else 0) - Complex.I*(lam:ℂ)*
    (shiftJacobian τ (fun i => p (θ i)) (fun i => m (θ i))
      (fun i => deriv p (θ i)) (fun i => deriv m (θ i)) i j : ℂ)

theorem fullAngularJacobian_column_sum {N : ℕ} (τ lam : ℝ) (p m : ℝ → ℝ)
    (θ : Fin N → ℝ) (j : Fin N) : ∑ i, fullAngularJacobian τ lam p m θ i j = 1 := by
  simp only [fullAngularJacobian, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Complex.ofReal_sum, shiftJacobian_column_sum, Complex.ofReal_zero, mul_zero,
    sub_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The determinant's nonnegative permutation weights are bounded by all
functions, exactly giving the product of column sums. -/
theorem permutation_weight_sum_le_columns {N : ℕ}
    (w : Fin N → Fin N → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    (∑ σ : Equiv.Perm (Fin N), ∏ j, w (σ j) j) ≤ ∏ j, ∑ i, w i j := by
  rw [Fintype.prod_sum]
  have hi : Function.Injective (fun σ : Equiv.Perm (Fin N) => (fun j => σ j)) := by
    intro σ ρ h
    exact Equiv.ext (fun j => congrFun h j)
  exact Finset.sum_le_sum_of_injOn (fun σ : Equiv.Perm (Fin N) => (fun j => σ j))
    hi.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
    (fun f _ _ => Finset.prod_nonneg (fun j _ => hw (f j) j))

end
end IsingBulk.Preferred22
