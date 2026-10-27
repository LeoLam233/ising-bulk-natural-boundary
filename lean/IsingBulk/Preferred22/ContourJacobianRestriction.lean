import IsingBulk.Preferred22.ContourJacobian

/-! The literal constrained Fréchet derivative has exactly the full balanced
Jacobian's determinant; the quotient direction is fixed with eigenvalue one. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem constrainedAngularJacobian_entry_eq_full {n : ℕ}
    (τ lam : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (θ : Fin n → ℝ) (q j : Fin n) :
    constrainedAngularJacobian τ lam p m θ q j =
      fullAngularJacobian τ lam p m (constrainedAngles θ) j.castSucc q.castSucc -
      fullAngularJacobian τ lam p m (constrainedAngles θ) j.castSucc (Fin.last n) := by
  rw [constrainedAngularJacobian_entry τ lam p m hp hm]
  unfold fullAngularJacobian shiftJacobian constrainedShiftEntry occupancy
  simp only [constrainedAngles, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.castSucc_ne_last, ite_false, Fin.castSucc_inj]
  by_cases hqj : q=j
  · subst j
    simp only [ite_true]
    push_cast
    ring
  · simp only [hqj, Ne.symm hqj, ite_false]
    push_cast
    ring

theorem constrainedAngularJacobian_det_eq_full {n : ℕ}
    (τ lam : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (θ : Fin n → ℝ) :
    (constrainedAngularJacobian τ lam p m θ).det =
      (fullAngularJacobian τ lam p m (constrainedAngles θ)).det := by
  let A := fullAngularJacobian τ lam p m (constrainedAngles θ)
  let B : Matrix (Fin n) (Fin n) ℂ := fun i j =>
    A i.castSucc j.castSucc - A i.castSucc (Fin.last n)
  have he : constrainedAngularJacobian τ lam p m θ = B.transpose := by
    ext q j
    exact constrainedAngularJacobian_entry_eq_full τ lam p m hp hm θ q j
  rw [he, Matrix.det_transpose]
  exact (determinant_restrict_sum_hyperplane A
    (fullAngularJacobian_column_sum τ lam p m (constrainedAngles θ))).symm

end
end IsingBulk.Preferred22
