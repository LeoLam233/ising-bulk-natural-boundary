import IsingBulk.Tail.SelectorDefinitions
import IsingBulk.Tail.SelectorJacobian

/-! Exact normalization and canceled-pair attachment on the original torus. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators

 theorem canceledPairProduct_eq {N : ℕ} (s : ℂ) (z y : Fin N → ℂ)
    (hy : ∀ i, y i ≠ 0) (hz : ∀ i, z i ≠ 0)
    (hroot : ∀ i, (z i)^2-(2*sourceS s-y i-(y i)⁻¹)*z i+1=0)
    (hygap : ∀ i j, 1-y i*y j ≠ 0) (hzgap : ∀ i j, 1-z i*z j ≠ 0) :
    canceledPairProduct z y = pairProduct z*pairProduct y := by
  unfold canceledPairProduct pairProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact (source_pair_identity (hy i) (hy j) (hz i) (hz j)
    (hroot i) (hroot j) (hygap i j) (hzgap i j)).symm

 theorem canceledReducedDensity_original {N : ℕ} {r : ℝ} {s : ℂ}
    {y z : Fin N → ℂ} (h : ResidueAdmissible r s y z) :
    canceledReducedDensity z y = reducedDensity z y := by
  have hy : ∀ i, ‖y i‖ < 1 := fun i => (h.y_on_circle i).trans_lt h.radius_lt_one
  have hz : ∀ i, ‖z i‖ < 1 := fun i => (h.root_inside i).trans h.radius_lt_one
  unfold canceledReducedDensity reducedDensity
  rw [canceledPairProduct_eq s z y h.y_ne_zero h.root_ne_zero h.root_quadratic
    (fun i j => one_sub_mul_ne_zero_of_norm_lt_one (hy i) (hy j))
    (fun i j => one_sub_mul_ne_zero_of_norm_lt_one (hz i) (hz j))]
  ring

 theorem deformedPoint_zero {N : ℕ} (f : SelectorFunctions) (r τ : ℝ)
    (θ : Fin N → ℝ) : deformedPoint f r τ 0 θ = angleTuple r θ := by
  funext i
  simp [deformedPoint, angleTuple, anglePoint, circleMap, mul_comm]

 theorem angularJacobian_zero {N : ℕ} (f : SelectorFunctions) (τ : ℝ) (θ : Fin N → ℝ) :
    angularJacobian f τ 0 θ = Matrix.diagonal (fun _ => Complex.I) := by
  ext i j
  simp [angularJacobian, retractionJacobian, Matrix.diagonal_apply]

 theorem pulledDensity_original {N : ℕ} (f : SelectorFunctions) (r τ : ℝ)
    (s : ℂ) (θ : Fin N → ℝ)
    (h : ResidueAdmissible r s (angleTuple r θ) (fun i => globalRoot s (anglePoint r (θ i)))) :
    pulledDensity f r τ 0 s θ = (N.factorial:ℂ)⁻¹*angleProductJacobian r θ*
      reducedDensity (fun i => globalRoot s (anglePoint r (θ i))) (angleTuple r θ) := by
  unfold pulledDensity
  rw [deformedPoint_zero, angularJacobian_zero, Matrix.det_diagonal]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show (fun i => globalRoot s (angleTuple r θ i)) =
      (fun i => globalRoot s (anglePoint r (θ i))) by rfl,
    canceledReducedDensity_original h]
  have he : (2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*Complex.I^N = (2*(Real.pi:ℂ))⁻¹^N := by
    rw [zpow_neg, zpow_natCast, mul_pow, mul_inv_rev]
    have hi : Complex.I^N ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
    rw [mul_assoc, mul_left_comm, inv_mul_cancel₀ hi, mul_one, inv_pow]
  unfold angleProductJacobian angleJacobian
  simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  change (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*Complex.I^N*
    (∏ i, anglePoint r (θ i))*_ = _
  rw [mul_assoc (N.factorial:ℂ)⁻¹, he]
  simp only [div_eq_mul_inv, inv_pow]
  ring

end
end IsingBulk.Tail
