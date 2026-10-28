import IsingBulk.HT22.Algebra.BorderedKernel

/-! # The exact odd constant-border determinant

This is the F001 odd identity, with every physical pair and collision retained.
The auxiliary roots are eliminated from the final theorem's statement.
-/

namespace IsingBulk.HT22.Algebra
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

section Dispersion
variable {N : ℕ} (S : ℂ) (y z r : Fin N → ℂ)
    (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hcurve : ∀ i, y i+(y i)⁻¹+z i+(z i)⁻¹ = 2*S)
    (hden : ∀ i j, i ≠ j → 1-z i*z j ≠ 0)
    (hroot : ∀ i, r i^2 = z i/y i)
include S hy hz hcurve hden hroot

/-- Ordinary four-point equations, including repeated indices. This adapter
exposes the already proved dispersion equation to the enlarged matrix. -/
theorem dispersionMatrix_four_point :
    ∀ a b i j,
      dispersionMatrix y z r a b*dispersionMatrix y z r i j-
        dispersionMatrix y z r a i*dispersionMatrix y z r b j+
        dispersionMatrix y z r a j*dispersionMatrix y z r b i =
      dispersionMatrix y z r a b*dispersionMatrix y z r a i*
        dispersionMatrix y z r a j*dispersionMatrix y z r b i*
        dispersionMatrix y z r b j*dispersionMatrix y z r i j := by
  intro a b i j
  by_cases hc : a=b ∨ a=i ∨ a=j ∨ b=i ∨ b=j ∨ i=j
  · exact four_point_of_index_collision _ (dispersionMatrix_diagonal y z r)
      (dispersionMatrix_skew y z r) a b i j hc
  push Not at hc
  obtain ⟨hab, hai, haj, hbi, hbj, hij⟩ := hc
  exact four_point_physical S (y a) (y b) (y i) (y j)
    (z a) (z b) (z i) (z j) (r a) (r b) (r i) (r j)
    (hy a) (hy b) (hy i) (hy j) (hz a) (hz b) (hz i) (hz j)
    (hcurve a) (hcurve b) (hcurve i) (hcurve j)
    (hden a b hab) (hden a i hai) (hden a j haj)
    (hden b i hbi) (hden b j hbj) (hden i j hij)
    (hroot a) (hroot b) (hroot i) (hroot j)

/-- The new ghost equation at all triples, including physical collisions. -/
theorem dispersionMatrix_three_point :
    ∀ a b c,
      r a*dispersionMatrix y z r b c-r b*dispersionMatrix y z r a c+
        r c*dispersionMatrix y z r a b =
      r a*r b*r c*dispersionMatrix y z r a b*
        dispersionMatrix y z r a c*dispersionMatrix y z r b c := by
  intro a b c
  by_cases hab : a=b
  · subst b; simp [dispersionMatrix_diagonal]
  by_cases hac : a=c
  · subst c
    rw [dispersionMatrix_diagonal, dispersionMatrix_skew y z r b a]
    ring
  by_cases hbc : b=c
  · subst c; simp [dispersionMatrix_diagonal]
  apply scaled_three_point
  rw [hroot a, hroot b, hroot c]
  exact three_point_dispersion S (y a) (y b) (y c) (z a) (z b) (z c)
    (hy a) (hy b) (hy c) (hz a) (hz b) (hz c)
    (hcurve a) (hcurve b) (hcurve c)
    (hden a b hab) (hden a c hac) (hden b c hbc)

end Dispersion

/-- The ordinary rational matrix with a ghost-first constant border. -/
def constantBorderFirst {N : ℕ} (y z : Fin N → ℂ) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  ghostBorder (fun i j => ordinaryEntry (y i) (y j) (z i) (z j)) (fun _ => 1)

/-- Exact finite diagonal congruence. -/
theorem normalizedBorder_eq_congruence {N : ℕ} (y z r : Fin N → ℂ) :
    ghostBorder (dispersionMatrix y z r) r =
      Matrix.diagonal (Fin.cons 1 r) * constantBorderFirst y z *
        Matrix.diagonal (Fin.cons 1 r) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [constantBorderFirst, ghostBorder, dispersionMatrix, scaledPair, ordinaryEntry]
  ring

/-- The normalized bordered determinant at every odd physical order. -/
theorem normalizedBorder_determinant (n : ℕ) (S : ℂ)
    (y z r : Fin (2*n+1) → ℂ)
    (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hcurve : ∀ i, y i+(y i)⁻¹+z i+(z i)⁻¹ = 2*S)
    (hden : ∀ i j, i ≠ j → 1-z i*z j ≠ 0)
    (hroot : ∀ i, r i^2 = z i/y i) :
    (ghostBorder (dispersionMatrix y z r) r).det =
      (∏ i, r i^2) * ∏ i, ∏ j ∈ Finset.Ioi i,
        physicalPair (y i) (y j) (z i) (z j) := by
  have h := determinant_squared_pair_product (n+1)
    (ghostBorder (dispersionMatrix y z r) r)
    (ghostBorder_diagonal _ _ (dispersionMatrix_diagonal y z r))
    (ghostBorder_skew _ _ (dispersionMatrix_skew y z r))
    (ghostBorder_four_point _ _
      (dispersionMatrix_four_point S y z r hy hz hcurve hden hroot)
      (dispersionMatrix_three_point S y z r hy hz hcurve hden hroot))
  rw [h]
  change upperPairProduct (fun i j =>
    (ghostBorder (dispersionMatrix y z r) r i j)^2) = _
  rw [upperPairProduct_succ (N := 2*n+1)]
  simp only [ghostBorder_zero_succ, upperPairProduct, Matrix.submatrix_apply,
    ghostBorder_succ_succ, dispersionMatrix, scaledPair_sq _ _ _ _ _ _ (hroot _) (hroot _)]

/-- F001's odd identity with the auxiliary roots fully eliminated. -/
theorem odd_constantBorderFirst_determinant (n : ℕ) (S : ℂ)
    (y z : Fin (2*n+1) → ℂ)
    (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hcurve : ∀ i, y i+(y i)⁻¹+z i+(z i)⁻¹ = 2*S)
    (hden : ∀ i j, i ≠ j → 1-z i*z j ≠ 0) :
    (constantBorderFirst y z).det =
      ∏ i, ∏ j ∈ Finset.Ioi i, physicalPair (y i) (y j) (z i) (z j) := by
  let r : Fin (2*n+1) → ℂ := fun i => Complex.sqrt (z i/y i)
  have hroot : ∀ i, r i^2 = z i/y i := by
    intro i
    exact Complex.cpow_nat_inv_pow (z i/y i) (by decide : 2 ≠ 0)
  have hr : ∀ i, r i ≠ 0 := by
    intro i hi
    have h := hroot i
    rw [hi, zero_pow (by decide : 2 ≠ 0)] at h
    exact div_ne_zero (hz i) (hy i) h.symm
  have hprod : (∏ i, r i)^2 ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun i _ => hr i))
  have h := normalizedBorder_determinant n S y z r hy hz hcurve hden hroot
  rw [normalizedBorder_eq_congruence, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Fin.prod_univ_succ] at h
  simp only [Fin.cons_zero, Fin.cons_succ, one_mul] at h
  rw [Finset.prod_pow] at h
  apply mul_left_cancel₀ hprod
  linear_combination h

end
end IsingBulk.HT22.Algebra
