import IsingBulk.Preferred22.MarkedMinorAlgebra
import IsingBulk.Anisotropic.Algebra.DeterminantBound

/-! A genuine complementary-minor Hadamard bound.  Row normalization preserves
the power `a^(N-ell)` of the unmarked kernel size.  The dimension factor differs
from the sharp complementary-size bound only by a fixed-order polynomial. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem norm_det_sq_le_row_entry_weights {N : ℕ} (hN : 0<N)
    (A : Matrix (Fin N) (Fin N) ℂ) (w : Fin N → ℝ)
    (hw : ∀ i, 0<w i) (hA : ∀ i j, ‖A i j‖ ≤ w i) :
    ‖A.det‖^2 ≤ (N:ℝ)^N * (∏ i, w i)^2 := by
  classical
  let B : Matrix (Fin N) (Fin N) ℂ := fun i j => A i j / (w i:ℂ)
  have hB : ∀ i j, ‖B i j‖ ≤ 1 := by
    intro i j
    dsimp [B]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hw i).le]
    exact (div_le_one (hw i)).mpr (hA i j)
  have he : A = Matrix.of (fun i j => (w i:ℂ)*B i j) := by
    ext i j
    change A i j = (w i:ℂ)*(A i j/(w i:ℂ))
    field_simp [Complex.ofReal_ne_zero.mpr (hw i).ne']
  have hd : A.det = (∏ i, (w i:ℂ))*B.det := by
    conv_lhs => rw [he]
    exact Matrix.det_mul_column _ _
  have hp : ‖∏ i, (w i:ℂ)‖ = ∏ i, w i := by
    rw [norm_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp only [Complex.norm_real, Real.norm_of_nonneg (hw i).le]
  have hb := IsingBulk.Anisotropic.Algebra.norm_det_sq_le_entry_bound B (by norm_num) hB
    (by simpa using hN)
  simp only [Fintype.card_fin, one_pow, mul_one] at hb
  rw [hd, norm_mul, hp, mul_pow]
  calc
    (∏ i, w i)^2 * ‖B.det‖^2 ≤ (∏ i, w i)^2 * (N:ℝ)^N :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

theorem product_unmarked_weight {N ell : ℕ} (e : Fin ell ↪ Fin N) (a : ℝ) :
    (∏ i : Fin N, if i ∈ Set.range e then 1 else a) = a^(N-ell) := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have hc : Fintype.card {i : Fin N // i ∉ Set.range e} = N-ell := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin, Fintype.card_range]
  simpa only [Fintype.card_subtype] using hc

/-- Fixed marked minors retain exactly one kernel-size factor for each
unmarked row, with no division by a matrix entry and no nonzero determinant
hypothesis. Repeated row or column marks are covered. -/
theorem markedDeterminant_hadamard_sq {N ell : ℕ} (hN : 0<N)
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : Fin ell → Fin N × Fin N)
    (a : ℝ) (ha : 0<a) (hK : ∀ i j, ‖K i j‖ ≤ a) :
    ‖markedDeterminant K marks‖^2 ≤ (N:ℝ)^N * a^(2*(N-ell)) := by
  classical
  by_cases hrow : Function.Injective (fun r => (marks r).1)
  · rw [markedDeterminant_eq_row_replacement K marks hrow]
    let e := markedRowEmbedding marks hrow
    let A := replacedRows K (fun r => Matrix.single (marks r).1 (marks r).2 (1:ℂ)) e
    let w : Fin N → ℝ := fun i => if i ∈ Set.range e then 1 else a
    have hw : ∀ i, 0<w i := by
      intro i
      dsimp [w]
      split_ifs <;> positivity
    have hA : ∀ i j, ‖A i j‖ ≤ w i := by
      intro i j
      by_cases hi : i ∈ Set.range e
      · obtain ⟨r,rfl⟩ := hi
        change ‖replacedRows K (fun r => Matrix.single (marks r).1 (marks r).2 (1:ℂ))
          (markedRowEmbedding marks hrow) (marks r).1 j‖ ≤ _
        rw [marked_replacedRows_selected]
        simp only [w, Set.mem_range_self, ite_true, Pi.single_apply]
        split_ifs <;> norm_num
      · simpa only [A, replacedRows, hi, dite_false, w, ite_false] using hK i j
    have hb := norm_det_sq_le_row_entry_weights hN A w hw hA
    have hp : (∏ i, w i)=a^(N-ell) := product_unmarked_weight e a
    rw [hp] at hb
    simpa only [A, e, ←pow_mul, Nat.mul_comm (N-ell) 2] using hb
  · simp only [Function.Injective] at hrow
    push Not at hrow
    obtain ⟨r,t,hrt,hne⟩ := hrow
    rw [markedDeterminant_eq_zero_of_row_collision K marks r t hne hrt]
    simp only [norm_zero, zero_pow (by omega : 2≠0)]
    positivity

theorem markedDeterminant_hadamard {N ell : ℕ} (hN : 0<N)
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : Fin ell → Fin N × Fin N)
    (a : ℝ) (ha : 0<a) (hK : ∀ i j, ‖K i j‖ ≤ a) :
    ‖markedDeterminant K marks‖ ≤ (Real.sqrt N)^N * a^(N-ell) := by
  have hb := markedDeterminant_hadamard_sq hN K marks a ha hK
  have hs : ((Real.sqrt N)^N*a^(N-ell))^2 = (N:ℝ)^N*a^(2*(N-ell)) := by
    rw [mul_pow, ←pow_mul, Nat.mul_comm N 2, pow_mul,
      Real.sq_sqrt (Nat.cast_nonneg N), ←pow_mul, Nat.mul_comm (N-ell) 2]
  rw [←hs] at hb
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb

end
end IsingBulk.Preferred22
