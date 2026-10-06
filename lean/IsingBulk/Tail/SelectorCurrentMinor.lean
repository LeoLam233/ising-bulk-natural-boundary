import IsingBulk.Tail.SelectorJacobian
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Actual replacement minor on the named current support. Its sign is
inherited from the unchanged angular column order. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

 theorem det_updateCol_isolated_row {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (q : Fin N) (v : Fin N → ℂ) (hrow : ∀ i, i ≠ q → A q i = 0) :
    (A.updateCol q v).det*A q q = v q*A.det := by
  cases N with
  | zero => exact Fin.elim0 q
  | succ n =>
    have hA : A.det = (-1:ℂ)^(q.val+q.val)*A q q*
        (A.submatrix q.succAbove q.succAbove).det := by
      rw [Matrix.det_succ_row A q]
      apply Finset.sum_eq_single q
      · intro i _ hi
        rw [hrow i hi, mul_zero, zero_mul]
      · simp
    have hB : (A.updateCol q v).det = (-1:ℂ)^(q.val+q.val)*v q*
        (A.submatrix q.succAbove q.succAbove).det := by
      rw [Matrix.det_succ_row (A.updateCol q v) q]
      rw [Finset.sum_eq_single q]
      · simp only [Matrix.updateCol_apply, ite_true,
          Matrix.submatrix_updateCol_succAbove]
      · intro i _ hi
        simp only [Matrix.updateCol_apply, hi, ite_false, hrow i hi, mul_zero, zero_mul]
      · simp
    rw [hA,hB]
    ring

 theorem retraction_named_minor {N : ℕ} (lam τ : ℝ) (p m p' m' : Fin N → ℝ)
    (q : Fin N) (hp : p q = 1) (hp' : p' q = 0) (hm : m q = 0) (hm' : m' q = 0) :
    ((retractionJacobian lam τ p m p' m').updateCol q
      (fun i => (retractionShift τ p m i:ℂ))).det =
        2*Complex.I*(τ:ℂ)*(retractionJacobian lam τ p m p' m').det := by
  have hrow := retractionJacobian_named_row lam τ p m p' m' q hp' hm hm'
  have he := det_updateCol_isolated_row (retractionJacobian lam τ p m p' m') q
    (fun i => (retractionShift τ p m i:ℂ)) (fun i hi => by
      rw [hrow i, ite_eq_right (Ne.symm hi)])
  rw [hrow q, ite_eq_left rfl, retractionShift_named τ p m q hp hm] at he
  apply (mul_right_cancel₀ Complex.I_ne_zero)
  calc
    _ = ((-2*τ:ℝ):ℂ)*(retractionJacobian lam τ p m p' m').det := he
    _ = _ := by push_cast; ring_nf; simp [Complex.I_sq]

end
end IsingBulk.Tail
