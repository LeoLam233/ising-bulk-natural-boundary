import IsingBulk.Preferred22.ContourMatrix
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.RealDeriv

/-! Fixed determinant jets with the actual diagonal/off-diagonal weights.
The permutation sum is bounded by the product of column sums, so this theorem
does not introduce an N! loss. No inverse matrix or nonzero entry is assumed. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem norm_iteratedFDeriv_product_weighted
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq ι]
    (s : Finset ι) (f : ι → E → ℂ) (x : E) (k : ℕ) (B : ι → ℝ)
    (_hB : ∀ i ∈ s, 0 ≤ B i) (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ s, ∀ r ≤ k, ‖iteratedFDeriv ℝ r (f i) x‖ ≤ B i) :
    ‖iteratedFDeriv ℝ k (fun y => ∏ i ∈ s, f i y) x‖ ≤
      (s.card:ℝ)^k * ∏ i ∈ s, B i := by
  apply (norm_iteratedFDeriv_prod_le hf (x := x) (n := k) (by simp)).trans
  calc
    _ ≤ ∑ p ∈ s.sym k, ((p : Multiset ι).countPerms:ℝ) * ∏ i ∈ s, B i := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i hi
      exact hb i hi _ ((Multiset.count_le_card i p).trans_eq p.property)
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      simpa using (Finset.sum_pow (s := s) (fun _ : ι => (1:ℝ)) k).symm

theorem norm_iteratedFDeriv_determinant_column_weighted
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
    (A : E → Matrix (Fin N) (Fin N) ℂ) (x : E) (k : ℕ)
    (w : Fin N → Fin N → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun y => A y i j))
    (hb : ∀ i j, ∀ r ≤ k, ‖iteratedFDeriv ℝ r (fun y => A y i j) x‖ ≤ w i j) :
    ‖iteratedFDeriv ℝ k (fun y => (A y).det) x‖ ≤
      (N:ℝ)^k * ∏ j, ∑ i, w i j := by
  have hprod (σ : Equiv.Perm (Fin N)) :
      ContDiff ℝ ∞ (fun y => ∏ j, A y (σ j) j) :=
    contDiff_prod (fun j _ => hA (σ j) j)
  have hsmooth (σ : Equiv.Perm (Fin N)) : ContDiff ℝ ∞
      (fun y => (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ∏ j, A y (σ j) j) :=
    (hprod σ).const_smul ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ))
  have hterm (σ : Equiv.Perm (Fin N)) :
      ‖iteratedFDeriv ℝ k
        (fun y => (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ∏ j, A y (σ j) j) x‖ ≤
      (N:ℝ)^k * ∏ j, w (σ j) j := by
    have hc : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)‖=1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with he | he <;> simp [he]
    change ‖iteratedFDeriv ℝ k
      (fun y => (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) • (∏ j, A y (σ j) j)) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hprod σ).of_le (by simp)).contDiffAt,
      norm_smul, hc, one_mul]
    simpa using norm_iteratedFDeriv_product_weighted Finset.univ
      (fun j y => A y (σ j) j) x k (fun j => w (σ j) j)
      (fun j _ => hw (σ j) j) (fun j _ => hA (σ j) j) (fun j _ => hb (σ j) j)
  simp only [Matrix.det_apply']
  rw [iteratedFDeriv_fun_sum_apply (fun σ _ => ((hsmooth σ).of_le (by simp)).contDiffAt)]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin N),
        ‖iteratedFDeriv ℝ k
          (fun y => (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ∏ j, A y (σ j) j) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ σ : Equiv.Perm (Fin N), (N:ℝ)^k * ∏ j, w (σ j) j :=
      Finset.sum_le_sum (fun σ _ => hterm σ)
    _ = (N:ℝ)^k * ∑ σ : Equiv.Perm (Fin N), ∏ j, w (σ j) j := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (permutation_weight_sum_le_columns w hw) (by positivity)

theorem norm_iteratedFDeriv_determinant_column_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
    (A : E → Matrix (Fin N) (Fin N) ℂ) (x : E) (k : ℕ)
    (w : Fin N → Fin N → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun y => A y i j))
    (hb : ∀ i j, ∀ r ≤ k, ‖iteratedFDeriv ℝ r (fun y => A y i j) x‖ ≤ w i j)
    {C : ℝ} (_hC : 0 ≤ C) (hcol : ∀ j, ∑ i, w i j ≤ C) :
    ‖iteratedFDeriv ℝ k (fun y => (A y).det) x‖ ≤ C^N * (N:ℝ)^k := by
  have hp : (∏ j, ∑ i, w i j) ≤ C^N := by
    simpa using Finset.prod_le_prod₀
      (fun j (_ : j∈Finset.univ) => Finset.sum_nonneg (fun i _ => hw i j))
      (fun j (_ : j∈Finset.univ) => hcol j)
  exact (norm_iteratedFDeriv_determinant_column_weighted A x k w hw hA hb).trans
    ((mul_le_mul_of_nonneg_left hp (by positivity : 0≤(N:ℝ)^k)).trans_eq (mul_comm _ _))

end
end IsingBulk.Preferred22
