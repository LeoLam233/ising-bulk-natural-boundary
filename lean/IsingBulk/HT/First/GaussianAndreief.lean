import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Fintype.Perm

/-! Finite Fubini for two polynomial-evaluation determinants.  The factorial
is obtained from the full permutation sum; no determinant integral identity
is assumed.  The two matrices may be different and the weight need not be
positive. -/
namespace IsingBulk.HT.First.Gaussian
noncomputable section
open MeasureTheory Matrix Equiv
open scoped BigOperators
set_option maxHeartbeats 1200000

private def permutationSign {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℝ :=
  ((Equiv.Perm.sign σ : ℤ) : ℝ)

private theorem permutationSign_mul_self {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permutationSign σ * permutationSign σ = 1 := by
  unfold permutationSign
  exact_mod_cast Int.isUnit_mul_self (Equiv.Perm.sign σ).isUnit

/-- Actual absolute integrability of the determinant product, proved by
finite expansion into products of one-dimensional integrable factors. -/
theorem weighted_determinants_integrable (n : ℕ) (f g : Fin n → ℝ → ℝ) (w : ℝ → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t * w t)) :
    Integrable (fun x : Fin n → ℝ =>
      (Matrix.of (fun i j => f i (x j))).det *
        (Matrix.of (fun i j => g i (x j))).det * ∏ i, w (x i)) := by
  classical
  let T := fun (σ τ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) =>
    (permutationSign σ * permutationSign τ) *
      ∏ i, f (σ i) (x i) * g (τ i) (x i) * w (x i)
  have hT (σ τ : Equiv.Perm (Fin n)) : Integrable (T σ τ) :=
    (Integrable.fintype_prod (fun i => hfg (σ i) (τ i))).const_mul _
  have hh := integrable_finsetSum Finset.univ (fun σ _ =>
    integrable_finsetSum Finset.univ (fun τ _ => hT σ τ))
  apply hh.congr
  filter_upwards [] with x
  symm
  simp only [Matrix.det_apply',Matrix.of_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  dsimp [T,permutationSign]
  simp only [Finset.prod_mul_distrib]
  ring

/-- Weighted finite Andreief identity.  Each one-dimensional cross product
is integrable; finite sums and product Fubini supply all higher-dimensional
integrability used in the proof. -/
theorem weighted_andreief (n : ℕ) (f g : Fin n → ℝ → ℝ) (w : ℝ → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t * w t)) :
    (∫ x : Fin n → ℝ,
      (Matrix.of (fun i j => f i (x j))).det *
        (Matrix.of (fun i j => g i (x j))).det * ∏ i, w (x i)) =
      (n.factorial : ℝ) *
        (Matrix.of (fun i j => ∫ t : ℝ, f i t * g j t * w t)).det := by
  classical
  let G : Matrix (Fin n) (Fin n) ℝ := fun i j => ∫ t : ℝ, f i t * g j t * w t
  let T := fun (σ τ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) =>
    (permutationSign σ * permutationSign τ) *
      ∏ i, f (σ i) (x i) * g (τ i) (x i) * w (x i)
  have hT (σ τ : Equiv.Perm (Fin n)) : Integrable (T σ τ) := by
    exact (Integrable.fintype_prod (fun i => hfg (σ i) (τ i))).const_mul _
  have hpoint (x : Fin n → ℝ) :
      (Matrix.of (fun i j => f i (x j))).det *
        (Matrix.of (fun i j => g i (x j))).det * ∏ i, w (x i) =
        ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n), T σ τ x := by
    simp only [Matrix.det_apply',Matrix.of_apply,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    dsimp [T,permutationSign]
    simp only [Finset.prod_mul_distrib]
    ring
  have hTint (σ τ : Equiv.Perm (Fin n)) :
      (∫ x : Fin n → ℝ, T σ τ x) =
        permutationSign σ * permutationSign τ * ∏ i, G (σ i) (τ i) := by
    dsimp only [T, G]
    rw [integral_const_mul]
    congr 1
    exact integral_fintype_prod_volume_eq_prod
      (fun i t => f (σ i) t * g (τ i) t * w t)
  have hrow (σ : Equiv.Perm (Fin n)) :
      (∑ τ : Equiv.Perm (Fin n), permutationSign τ * ∏ i, G (σ i) (τ i)) =
        permutationSign σ * G.det := by
    calc
      _ = (G.submatrix σ id).transpose.det := by
        rw [Matrix.det_apply']
        rfl
      _ = _ := by rw [Matrix.det_transpose,Matrix.det_permute]; rfl
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun τ _ => hT _ τ),hTint]
    calc
      _ = ∑ σ : Equiv.Perm (Fin n), permutationSign σ *
          (∑ τ : Equiv.Perm (Fin n), permutationSign τ * ∏ i, G (σ i) (τ i)) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro τ _
        ring
      _ = ∑ σ : Equiv.Perm (Fin n), G.det := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [hrow,← mul_assoc,permutationSign_mul_self,one_mul]
      _ = _ := by
        change (∑ _σ : Equiv.Perm (Fin n), G.det) = (n.factorial : ℝ) * G.det
        simp [Fintype.card_perm]
  · intro σ _
    exact integrable_finsetSum _ (fun τ _ => hT σ τ)

/-- The usual orientation of evaluation matrices: coordinates are rows,
polynomial labels are columns. -/
theorem weighted_andreief_coordinates (n : ℕ) (f g : Fin n → ℝ → ℝ) (w : ℝ → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * g j t * w t)) :
    (∫ x : Fin n → ℝ,
      (Matrix.of (fun i j => f j (x i))).det *
        (Matrix.of (fun i j => g j (x i))).det * ∏ i, w (x i)) =
      (n.factorial : ℝ) *
        (Matrix.of (fun i j => ∫ t : ℝ, f i t * g j t * w t)).det := by
  convert weighted_andreief n f g w hfg using 1
  apply integral_congr_ae
  filter_upwards [] with x
  have hf : (Matrix.of (fun i j => f j (x i))).det =
      (Matrix.of (fun i j => f i (x j))).det := Matrix.det_transpose _
  have hg : (Matrix.of (fun i j => g j (x i))).det =
      (Matrix.of (fun i j => g i (x j))).det := Matrix.det_transpose _
  rw [hf,hg]

/-- Orthogonal specialization. The factor n! includes the empty and
one-dimensional cases. -/
theorem weighted_orthogonal_determinant_square (n : ℕ) (f : Fin n → ℝ → ℝ)
    (w : ℝ → ℝ) (d : Fin n → ℝ)
    (hfg : ∀ i j, Integrable (fun t => f i t * f j t * w t))
    (horth : ∀ i j, (∫ t : ℝ, f i t * f j t * w t) = if i=j then d i else 0) :
    (∫ x : Fin n → ℝ,
      (Matrix.of (fun i j => f j (x i))).det^2 * ∏ i, w (x i)) =
      (n.factorial : ℝ) * ∏ i, d i := by
  rw [show (fun x : Fin n → ℝ =>
      (Matrix.of (fun i j => f j (x i))).det^2 * ∏ i, w (x i)) =
      (fun x : Fin n → ℝ =>
      (Matrix.of (fun i j => f j (x i))).det *
      (Matrix.of (fun i j => f j (x i))).det * ∏ i, w (x i)) by
        funext x; rw [pow_two]]
  rw [weighted_andreief_coordinates n f f w hfg]
  have hM : (Matrix.of (fun i j => ∫ t : ℝ, f i t * f j t * w t)) =
      Matrix.diagonal d := by
    ext i j
    simpa only [Matrix.of_apply,Matrix.diagonal_apply] using horth i j
  rw [hM,Matrix.det_diagonal]

/-- Monic polynomial Vandermonde integrability with only the genuine
one-dimensional cross-product assumptions. -/
theorem weighted_monic_vandermonde_integrable (n : ℕ) (p : Fin n → Polynomial ℝ)
    (w : ℝ → ℝ) (hdeg : ∀ i, (p i).natDegree=i.val) (hmonic : ∀ i, (p i).Monic)
    (hfg : ∀ i j, Integrable (fun t => (p i).eval t * (p j).eval t * w t)) :
    Integrable (fun x : Fin n → ℝ => (Matrix.vandermonde x).det^2 * ∏ i, w (x i)) := by
  have hh := weighted_determinants_integrable n (fun i t => (p i).eval t)
    (fun i t => (p i).eval t) w hfg
  apply hh.congr
  filter_upwards [] with x
  have hd := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x p hdeg hmonic
  have ht : (Matrix.of (fun i j => (p i).eval (x j))).det =
      (Matrix.of (fun i j => (p j).eval (x i))).det := Matrix.det_transpose _
  rw [ht,← hd,pow_two]

/-- Apply the existing monic polynomial evaluation determinant theorem;
no change-of-basis argument is reconstructed here. -/
theorem weighted_monic_vandermonde_square (n : ℕ) (p : Fin n → Polynomial ℝ)
    (w : ℝ → ℝ) (d : Fin n → ℝ)
    (hdeg : ∀ i, (p i).natDegree=i.val) (hmonic : ∀ i, (p i).Monic)
    (hfg : ∀ i j, Integrable (fun t => (p i).eval t * (p j).eval t * w t))
    (horth : ∀ i j, (∫ t : ℝ, (p i).eval t * (p j).eval t * w t) =
      if i=j then d i else 0) :
    (∫ x : Fin n → ℝ, (Matrix.vandermonde x).det^2 * ∏ i, w (x i)) =
      (n.factorial : ℝ) * ∏ i, d i := by
  have hdet (x : Fin n → ℝ) :=
    Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde x p hdeg hmonic
  simp_rw [hdet]
  exact weighted_orthogonal_determinant_square n (fun i t => (p i).eval t) w d hfg horth

end
end IsingBulk.HT.First.Gaussian
