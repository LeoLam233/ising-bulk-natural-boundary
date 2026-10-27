import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! The determinant bound required by Section 2 and the marked-minor estimates.
We derive the needed C^N N^(N/2) form from the Gram spectrum and AM--GM. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Matrix ComplexOrder
open Matrix

theorem nonnegative_product_le_mean_pow {N : ℕ} (hN : 0 < N)
    (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∏ i, a i) ≤ ((∑ i, a i)/(N : ℝ))^N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : Fin N => (N : ℝ)⁻¹) a
    (fun _ _ => inv_nonneg.mpr hNR.le)
    (by simp [hN0]) (fun i _ => ha i)
  have hp := pow_le_pow_left₀
    (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (ha i) _)) h N
  rw [← Finset.prod_pow] at hp
  simp_rw [Real.rpow_inv_natCast_pow (ha _) (by omega : N ≠ 0)] at hp
  simpa only [← Finset.mul_sum, div_eq_mul_inv, mul_comm (N : ℝ)⁻¹,
    ← Finset.sum_mul] using hp

theorem gram_det_eq_norm_det_sq {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    (Aᴴ*A).det = (‖A.det‖^2 : ℝ) := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose]
  exact Complex.normSq_eq_conj_mul_self.symm.trans
    (congrArg (fun r : ℝ => (r : ℂ)) (Complex.normSq_eq_norm_sq A.det))

theorem gram_trace_re {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    (Aᴴ*A).trace.re = ∑ i, ∑ j, ‖A j i‖^2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.star_def]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_conj_mul_self]
  exact Complex.normSq_eq_norm_sq _

/-- Hadamard's C^N N^(N/2) bound in squared form, sufficient for all N.
The proof uses the actual determinant, not a replacement matrix functional. -/
theorem determinant_bound_sq {N : ℕ} (hN : 0 < N)
    (A : Matrix (Fin N) (Fin N) ℂ) {C : ℝ} (_hC : 0 ≤ C)
    (hA : ∀ i j, ‖A i j‖ ≤ C) : ‖A.det‖^2 ≤ ((N : ℝ)*C^2)^N := by
  let H := Aᴴ*A
  have hH : H.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  let a : Fin N → ℝ := hH.isHermitian.eigenvalues
  have ha : ∀ i, 0 ≤ a i := hH.eigenvalues_nonneg
  have hd : ‖A.det‖^2 = ∏ i, a i := by
    have he := hH.isHermitian.det_eq_prod_eigenvalues
    rw [show H.det = (‖A.det‖^2 : ℝ) from gram_det_eq_norm_det_sq A] at he
    rw [← RCLike.ofReal_prod] at he
    exact RCLike.ofReal_injective he
  have ht : ∑ i, a i = H.trace.re := by
    have he := congrArg (RCLike.re : ℂ → ℝ) hH.isHermitian.trace_eq_sum_eigenvalues
    simpa only [map_sum, RCLike.ofReal_re, RCLike.re_eq_complex_re] using he.symm
  have htr : H.trace.re ≤ (N : ℝ)^2*C^2 := by
    rw [gram_trace_re]
    calc
      (∑ i, ∑ j, ‖A j i‖^2) ≤ ∑ _i : Fin N, ∑ _j : Fin N, C^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hA j i) _
      _ = _ := by simp; ring
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmean : (∑ i, a i)/(N : ℝ) ≤ (N : ℝ)*C^2 := by
    apply (div_le_iff₀ hNR).mpr
    rw [ht]
    nlinarith [htr]
  rw [hd]
  exact (nonnegative_product_le_mean_pow hN a ha).trans
    (pow_le_pow_left₀ (div_nonneg (Finset.sum_nonneg (fun i _ => ha i)) hNR.le) hmean _)

theorem determinant_bound {N : ℕ} (hN : 0 < N)
    (A : Matrix (Fin N) (Fin N) ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i j, ‖A i j‖ ≤ C) : ‖A.det‖ ≤ (Real.sqrt N*C)^N := by
  have h := determinant_bound_sq hN A hC hA
  have hsq : ((Real.sqrt N*C)^N)^2 = ((N : ℝ)*C^2)^N := by
    rw [← pow_mul, mul_comm N 2, pow_mul, mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith [norm_nonneg A.det, pow_nonneg (mul_nonneg (Real.sqrt_nonneg (N : ℝ)) hC) N]

end
end IsingBulk.Preferred22
