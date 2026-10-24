import IsingBulk.Anisotropic.Algebra.ArithmeticGeometric
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic

namespace IsingBulk.Anisotropic.Algebra
noncomputable section
open Matrix
open scoped BigOperators ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gram_det_re (A : Matrix ι ι ℂ) : (Aᴴ * A).det.re = ‖A.det‖^2 := by
  rw [Matrix.det_mul,Matrix.det_conjTranspose]
  simp only [Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  ring

omit [DecidableEq ι] in
theorem gram_trace_re (A : Matrix ι ι ℂ) :
    (Aᴴ * A).trace.re = ∑ i, ∑ j, ‖A j i‖^2 := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Complex.re_sum,Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  ring

/-- A determinant estimate from the Gram spectrum and uniform AM-GM.
It supplies the sharp N^(N/2) entry-bound exponent without a Pfaffian axiom. -/
theorem norm_det_sq_le_trace_mean_pow (A : Matrix ι ι ℂ)
    (hn : 0 < Fintype.card ι) :
    ‖A.det‖^2 ≤ (((Aᴴ*A).trace.re) / Fintype.card ι)^Fintype.card ι := by
  let hG := Matrix.isHermitian_conjTranspose_mul_self A
  have hd : (Aᴴ*A).det.re = ∏ i, hG.eigenvalues i := by
    have h := congrArg Complex.re hG.det_eq_prod_eigenvalues
    exact h.trans (by norm_cast)
  have ht : (Aᴴ*A).trace.re = ∑ i, hG.eigenvalues i := by
    have h := congrArg Complex.re hG.trace_eq_sum_eigenvalues
    simpa using h
  rw [← gram_det_re A,hd,ht]
  exact prod_le_arithmetic_mean_pow hG.eigenvalues
    (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A) hn

theorem norm_det_sq_le_entry_bound (A : Matrix ι ι ℂ) {C : ℝ}
    (_hC : 0 ≤ C) (hA : ∀ i j, ‖A i j‖ ≤ C) (hn : 0 < Fintype.card ι) :
    ‖A.det‖^2 ≤ ((Fintype.card ι:ℝ)*C^2)^Fintype.card ι := by
  have hnr : (0:ℝ) < Fintype.card ι := by exact_mod_cast hn
  have ht : (Aᴴ*A).trace.re ≤ (Fintype.card ι:ℝ)^2*C^2 := by
    rw [gram_trace_re]
    calc
      (∑ i, ∑ j, ‖A j i‖^2) ≤ ∑ _i : ι, ∑ _j : ι, C^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hA j i) 2
      _ = _ := by simp; ring
  have hmean : (Aᴴ*A).trace.re / Fintype.card ι ≤ (Fintype.card ι:ℝ)*C^2 := by
    apply (div_le_iff₀ hnr).mpr
    nlinarith [ht]
  exact (norm_det_sq_le_trace_mean_pow A hn).trans
    (pow_le_pow_left₀ (div_nonneg (by rw [gram_trace_re]; positivity) hnr.le) hmean _)

end
end IsingBulk.Anisotropic.Algebra
