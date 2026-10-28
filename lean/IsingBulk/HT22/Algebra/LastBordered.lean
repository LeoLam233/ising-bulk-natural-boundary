import IsingBulk.HT22.Algebra.OddBordered

/-! # The manuscript's last constant border and complete collision factor -/
namespace IsingBulk.HT22.Algebra
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Reversing both signs of a skew border leaves its determinant unchanged. -/
theorem ghostBorder_neg_det {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (r : Fin N → ℂ) :
    (ghostBorder K (fun i => -r i)).det = (ghostBorder K r).det := by
  let d : Fin (N+1) → ℂ := Fin.cons (-1) (fun _ => 1)
  have he : ghostBorder K (fun i => -r i) =
      Matrix.diagonal d * ghostBorder K r * Matrix.diagonal d := by
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp [d]
  rw [he, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  simp [d, Fin.prod_univ_succ]

/-- The exact F001 matrix: physical indices first and the constant ghost last. -/
def constantBorderLast {N : ℕ} (y z : Fin N → ℂ) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  (ghostBorder (fun i j => ordinaryEntry (y i) (y j) (z i) (z j))
    (fun _ => -1)).submatrix (finRotate (N+1)) (finRotate (N+1))

@[simp] theorem constantBorderLast_ordinary {N : ℕ} (y z : Fin N → ℂ) (i j : Fin N) :
    constantBorderLast y z i.castSucc j.castSucc = ordinaryEntry (y i) (y j) (z i) (z j) := by
  simp [constantBorderLast, Matrix.submatrix_apply]

@[simp] theorem constantBorderLast_upper {N : ℕ} (y z : Fin N → ℂ) (i : Fin N) :
    constantBorderLast y z i.castSucc (Fin.last N) = 1 := by
  simp [constantBorderLast, Matrix.submatrix_apply]

@[simp] theorem constantBorderLast_lower {N : ℕ} (y z : Fin N → ℂ) (j : Fin N) :
    constantBorderLast y z (Fin.last N) j.castSucc = -1 := by
  simp [constantBorderLast, Matrix.submatrix_apply]

@[simp] theorem constantBorderLast_ghost {N : ℕ} (y z : Fin N → ℂ) :
    constantBorderLast y z (Fin.last N) (Fin.last N) = 0 := by
  simp [constantBorderLast, Matrix.submatrix_apply]

/-- Exact permutation and sign-congruence equivalence, not a change of the observable. -/
theorem constantBorderLast_det_eq_first {N : ℕ} (y z : Fin N → ℂ) :
    (constantBorderLast y z).det = (constantBorderFirst y z).det := by
  rw [constantBorderLast, Matrix.det_submatrix_equiv_self]
  exact ghostBorder_neg_det _ (fun _ => 1)

/-- F001 Proposition 4.3 in the manuscript's precise last-border convention. -/
theorem odd_constantBorderLast_determinant (n : ℕ) (S : ℂ)
    (y z : Fin (2*n+1) → ℂ)
    (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hcurve : ∀ i, y i+(y i)⁻¹+z i+(z i)⁻¹ = 2*S)
    (hden : ∀ i j, i ≠ j → 1-z i*z j ≠ 0) :
    (constantBorderLast y z).det =
      ∏ i, ∏ j ∈ Finset.Ioi i, physicalPair (y i) (y j) (z i) (z j) := by
  rw [constantBorderLast_det_eq_first]
  exact odd_constantBorderFirst_determinant n S y z hy hz hcurve hden

/-- The explicit rational quotient of each squared collision zero. -/
def pairQuotient (yi yj zi zj : ℂ) : ℂ :=
  -(zi/yi)*(zj/yj)/(1-zi*zj)^2

theorem physicalPair_collision_factor (yi yj zi zj : ℂ) :
    physicalPair yi yj zi zj = (yi-yj)^2 * pairQuotient yi yj zi zj := by
  unfold physicalPair dispersionB pairQuotient
  rw [div_pow]
  ring

/-- The full squared Vandermonde, rather than isolated pairwise vanishing. -/
def squaredVandermonde {N : ℕ} (y : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, (y i-y j)^2

/-- Explicit quotient, enabling later fixed-chart regularity proofs. -/
def collisionQuotient {N : ℕ} (y z : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, pairQuotient (y i) (y j) (z i) (z j)

theorem completePairProduct_collision_factor {N : ℕ} (y z : Fin N → ℂ) :
    (∏ i, ∏ j ∈ Finset.Ioi i, physicalPair (y i) (y j) (z i) (z j)) =
      squaredVandermonde y * collisionQuotient y z := by
  simp only [physicalPair_collision_factor, Finset.prod_mul_distrib,
    squaredVandermonde, collisionQuotient]

/-- Complete algebraic collision factor of degree N(N−1), for every odd N. -/
theorem odd_constantBorderLast_collision_factor (n : ℕ) (S : ℂ)
    (y z : Fin (2*n+1) → ℂ)
    (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hcurve : ∀ i, y i+(y i)⁻¹+z i+(z i)⁻¹ = 2*S)
    (hden : ∀ i j, i ≠ j → 1-z i*z j ≠ 0) :
    (constantBorderLast y z).det = squaredVandermonde y * collisionQuotient y z := by
  rw [odd_constantBorderLast_determinant n S y z hy hz hcurve hden,
    completePairProduct_collision_factor]

end
end IsingBulk.HT22.Algebra
