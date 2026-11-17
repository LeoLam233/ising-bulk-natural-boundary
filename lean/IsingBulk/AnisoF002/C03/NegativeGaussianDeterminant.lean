import IsingBulk.AnisoF002.C03.NegativeGaussianOrthogonal
import IsingBulk.AnisoF002.RegularTail.VandermondeBlock
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The ordinary squared-Vandermonde Gaussian integral

The finite determinant is expanded into actual integrable products.  The
one-variable orthogonality proved in `NegativeGaussianOrthogonal` then
removes precisely the unequal permutations.  This constructs the Mehta
normalization from Fubini and Gaussian integration, with no imported
random-matrix or natural-boundary endpoint.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Polynomial Matrix
open scoped BigOperators

def gaussianPolynomialMatrix (n : ℕ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (monicGaussianPoly i.val).eval (x j)

def gaussianNorm (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n * (n.factorial : ℝ) * Real.sqrt Real.pi

def gaussianPermutationProduct {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : ℝ :=
  ∏ i, (monicGaussianPoly (σ i).val).eval (x i) *
    (monicGaussianPoly (τ i).val).eval (x i) * Real.exp (-(x i) ^ 2)

theorem gaussianPermutationProduct_integrable {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    Integrable (gaussianPermutationProduct σ τ) := by
  apply Integrable.fintype_prod (μ := fun _ : Fin n => volume)
    (f := fun i t => (monicGaussianPoly (σ i).val).eval t *
      (monicGaussianPoly (τ i).val).eval t * Real.exp (-t ^ 2))
  intro i
  simpa only [Polynomial.eval_mul] using
    polynomial_gaussian_integrable
      (monicGaussianPoly (σ i).val * monicGaussianPoly (τ i).val)

theorem gaussianPermutationProduct_integral {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    (∫ x : Fin n → ℝ, gaussianPermutationProduct σ τ x) =
      if σ = τ then ∏ i : Fin n, gaussianNorm i.val else 0 := by
  classical
  unfold gaussianPermutationProduct
  rw [integral_fintype_prod_volume_eq_prod
    (fun (i : Fin n) (t : ℝ) => (monicGaussianPoly (σ i).val).eval t *
      (monicGaussianPoly (τ i).val).eval t * Real.exp (-t ^ 2))]
  simp_rw [monicGaussianPoly_integral_product]
  by_cases h : σ = τ
  · subst τ
    simp only [ite_true]
    exact Equiv.prod_comp σ (fun i : Fin n => gaussianNorm i.val)
  · simp only [h, ite_false]
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
      by_contra hh
      apply h
      apply Equiv.ext
      intro i
      exact not_ne_iff.mp (not_exists.mp hh i)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hv : (σ i).val ≠ (τ i).val := fun he => hi (Fin.ext he)
    simp only [hv, ite_false]

theorem gaussianDeterminant_square_expansion {n : ℕ} (x : Fin n → ℝ) :
    (gaussianPolynomialMatrix n x).det ^ 2 * (∏ i, Real.exp (-(x i) ^ 2)) =
      ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          gaussianPermutationProduct σ τ x := by
  classical
  simp only [pow_two, Matrix.det_apply', Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  simp only [gaussianPermutationProduct, Finset.prod_mul_distrib,
    gaussianPolynomialMatrix]
  ring

theorem gaussianDeterminant_integrable (n : ℕ) :
    Integrable (fun x : Fin n → ℝ =>
      (gaussianPolynomialMatrix n x).det ^ 2 * (∏ i, Real.exp (-(x i) ^ 2))) := by
  simp_rw [gaussianDeterminant_square_expansion]
  apply integrable_finsetSum
  intro σ _
  apply integrable_finsetSum
  intro τ _
  exact (gaussianPermutationProduct_integrable σ τ).const_mul _

theorem gaussianDeterminant_integral (n : ℕ) :
    (∫ x : Fin n → ℝ,
      (gaussianPolynomialMatrix n x).det ^ 2 * (∏ i, Real.exp (-(x i) ^ 2))) =
        (n.factorial : ℝ) * ∏ i : Fin n, gaussianNorm i.val := by
  classical
  rw [show (fun x : Fin n → ℝ =>
      (gaussianPolynomialMatrix n x).det ^ 2 * (∏ i, Real.exp (-(x i) ^ 2))) =
      (fun x => ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          gaussianPermutationProduct σ τ x) from
    funext gaussianDeterminant_square_expansion]
  rw [integral_finsetSum]
  · have hinner (σ : Equiv.Perm (Fin n)) :
        (∫ x : Fin n → ℝ, ∑ τ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
            gaussianPermutationProduct σ τ x) = ∏ i : Fin n, gaussianNorm i.val := by
      rw [integral_finsetSum]
      · simp_rw [integral_const_mul, gaussianPermutationProduct_integral]
        rw [Finset.sum_eq_single σ]
        · simp only [ite_true]
          have hs : ((Equiv.Perm.sign σ : ℤ) : ℝ) *
              ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
            exact_mod_cast Int.units_coe_mul_self (Equiv.Perm.sign σ)
          rw [hs, one_mul]
        · intro τ _ hτσ
          simp only [Ne.symm hτσ, ite_false, mul_zero]
        · simp
      · intro τ _
        exact (gaussianPermutationProduct_integrable σ τ).const_mul _
    simp_rw [hinner]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin, nsmul_eq_mul]
  · intro σ _
    apply integrable_finsetSum
    intro τ _
    exact (gaussianPermutationProduct_integrable σ τ).const_mul _

theorem gaussianPolynomialMatrix_det {n : ℕ} (x : Fin n → ℝ) :
    (gaussianPolynomialMatrix n x).det = (Matrix.vandermonde x).det := by
  have h := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x
    (fun i : Fin n => monicGaussianPoly i.val)
    (fun i => (monicGaussianPoly_isMonicOfDegree i.val).natDegree_eq)
    (fun i => (monicGaussianPoly_isMonicOfDegree i.val).monic)
  calc
    (gaussianPolynomialMatrix n x).det = (gaussianPolynomialMatrix n x)ᵀ.det :=
      (Matrix.det_transpose _).symm
    _ = (Matrix.vandermonde x).det := h.symm

theorem vandermonde_det_sq {n : ℕ} (x : Fin n → ℝ) :
    (Matrix.vandermonde x).det ^ 2 = RegularTail.vandermondeSquared x := by
  classical
  rw [Matrix.det_vandermonde]
  simp only [← Finset.prod_pow]
  unfold RegularTail.vandermondeSquared Isotropic.indexPairs
  rw [Finset.prod_filter, Finset.prod_product]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.filter_lt_eq_Ioi, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j _
  split_ifs
  · ring
  · rfl

/-- The full ordinary Gaussian squared-Vandermonde integral, with all factorials. -/
theorem ordinary_gaussian_vandermonde_integral (n : ℕ) :
    (∫ x : Fin n → ℝ, Real.exp (-(∑ i, (x i) ^ 2)) *
      RegularTail.vandermondeSquared x) =
        (n.factorial : ℝ) * ∏ i : Fin n, gaussianNorm i.val := by
  have he (x : Fin n → ℝ) : Real.exp (-(∑ i, (x i) ^ 2)) *
      RegularTail.vandermondeSquared x =
      (gaussianPolynomialMatrix n x).det ^ 2 * (∏ i, Real.exp (-(x i) ^ 2)) := by
    rw [gaussianPolynomialMatrix_det, vandermonde_det_sq, ← Real.exp_sum,
      Finset.sum_neg_distrib, mul_comm]
  simp_rw [he]
  exact gaussianDeterminant_integral n

end
end IsingBulk.AnisoF002.NegativeHT.Angular
