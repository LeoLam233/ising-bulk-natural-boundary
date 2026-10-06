import IsingBulk.Tail.SelectorGeometry

/-! Rank-one angular Jacobian calculation, including the disjoint support
cancellation that prevents any uncontrolled occupancy determinant. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem diagonal_rankOne_det {n : ℕ} (d u v : Fin n → ℂ)
    (hd : ∀ i, d i ≠ 0) (huv : ∀ i, u i*v i = 0) :
    Matrix.det (fun i j => (if i=j then d i else 0)+u i*v j) =
      ∏ i, d i := by
  let a : Fin n → ℂ := fun i => u i/d i
  have he : (fun i j => (if i=j then d i else 0)+u i*v j : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal d * (1+Matrix.replicateCol Unit a*Matrix.replicateRow Unit v) := by
    ext i j
    rw [Matrix.diagonal_mul]
    simp only [Matrix.add_apply, Matrix.one_apply,
      Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply,
      Fintype.sum_unique, a]
    by_cases hij : i=j
    · subst j; simp only [ite_true]; field_simp [hd i]
    · simp only [hij, ite_false, zero_add]; field_simp [hd i]
  rw [he, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hz : v ⬝ᵥ a = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    dsimp [a]
    rw [← mul_div_assoc, mul_comm (v i) (u i), huv i, zero_div]
  rw [hz, add_zero, mul_one]

theorem retractionJacobian_det {N : ℕ} (lam τ : ℝ)
    (p m p' m' : Fin N → ℝ) (hdisjoint : ∀ i, m i*p' i = 0) :
    (retractionJacobian lam τ p m p' m').det =
      ∏ i, (Complex.I + (lam*(-2*τ*p' i+τ*occupancy p/(2*N)*m' i):ℝ)) := by
  let d : Fin N → ℂ := fun i => Complex.I +
    (lam*(-2*τ*p' i+τ*occupancy p/(2*N)*m' i):ℝ)
  let u : Fin N → ℂ := fun i => (lam*τ/(2*N)*m i:ℝ)
  let v : Fin N → ℂ := fun i => (p' i:ℂ)
  have hd : ∀ i, d i ≠ 0 := by
    intro i he
    have hi := congrArg Complex.im he
    change 1+0=0 at hi
    norm_num at hi
  have huv : ∀ i, u i*v i = 0 := by
    intro i
    dsimp [u,v]
    rw [← Complex.ofReal_mul]
    simp [mul_assoc, hdisjoint i]
  have he : retractionJacobian lam τ p m p' m' =
      (fun i j => (if i=j then d i else 0)+u i*v j) := by
    ext i j
    simp [retractionJacobian,d,u,v]
  rw [he, diagonal_rankOne_det d u v hd huv]

end
end IsingBulk.Tail
