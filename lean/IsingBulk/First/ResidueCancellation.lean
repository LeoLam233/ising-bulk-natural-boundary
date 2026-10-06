import IsingBulk.First.ResidueBounds

/-! Global removal of every apparent x=0 pole in the complete source density. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

def clearedNumerator {N : ℕ} (z y x : Fin N → ℂ) : ℂ :=
  (1 + coordinateProduct x / coordinateProduct y) /
    ((1-coordinateProduct x)*(1-coordinateProduct y)) *
      pairProduct x * pairProduct y * ∏ i, (-2:ℂ)/(x i-(z i)⁻¹)

theorem dispersion_inv_factorization {x y z s : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hroot : z^2-(2*sourceS s-y-y⁻¹)*z+1=0) :
    (dispersion x y s)⁻¹ = x * (x-z)⁻¹ * ((-2:ℂ)/(x-z⁻¹)) := by
  rw [dispersion_factorization hx hy hz hroot]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, inv_neg]
  ring

theorem doubleDensity_eq_cauchy {N : ℕ} {r : ℝ} {s : ℂ}
    {y z : Fin N → ℂ} (h : ResidueAdmissible r s y z)
    (x : Fin N → ℂ) (hx : ∀ i, x i ≠ 0) :
    doubleDensity s x y = (∏ i, (x i-z i)⁻¹) * clearedNumerator z y x := by
  have hX : coordinateProduct x ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hx i)
  have hp : (∏ i, (dispersion (x i) (y i) s)⁻¹) =
      coordinateProduct x * (∏ i, (x i-z i)⁻¹) * (∏ i, (-2:ℂ)/(x i-(z i)⁻¹)) := by
    simp_rw [dispersion_inv_factorization (hx _) (h.y_ne_zero _) (h.root_ne_zero _) (h.root_quadratic _)]
    simp only [Finset.prod_mul_distrib, coordinateProduct]
  have hc : ((coordinateProduct x)⁻¹+(coordinateProduct y)⁻¹)*coordinateProduct x =
      1+coordinateProduct x/coordinateProduct y := by
    rw [add_mul, inv_mul_cancel₀ hX]
    simp only [div_eq_mul_inv]
    ring
  unfold doubleDensity commonDensity clearedNumerator
  rw [hp]
  calc
    _ = (((coordinateProduct x)⁻¹+(coordinateProduct y)⁻¹)*coordinateProduct x) /
      ((1-coordinateProduct x)*(1-coordinateProduct y)) *
      pairProduct x * pairProduct y * (∏ i, (x i-z i)⁻¹) *
      (∏ i, (-2:ℂ)/(x i-(z i)⁻¹)) := by ring
    _ = _ := by rw [hc]; ring

theorem residueFactor_cleared {z : ℂ} (hz : z ≠ 0) :
    (-2:ℂ)/(z-z⁻¹) = z⁻¹ * residueFactor z := by
  by_cases hsq : 1-z^2 = 0
  · have he : z-z⁻¹ = 0 := by
      apply (mul_left_cancel₀ hz)
      rw [mul_sub, mul_inv_cancel₀ hz, mul_zero]
      linear_combination -hsq
    simp [residueFactor, hsq, he]
  · have he : z-z⁻¹ ≠ 0 := by
      intro he
      apply hsq
      have he' := congrArg (fun w : ℂ => z*w) he
      simp only [mul_sub, mul_inv_cancel₀ hz, mul_zero] at he'
      linear_combination -he'
    unfold residueFactor
    have hsq' : z^2-1 ≠ 0 := by intro he; apply hsq; linear_combination -he
    field_simp
    ring

theorem clearedNumerator_at_roots {N : ℕ} {z y : Fin N → ℂ}
    (hz : ∀ i, z i ≠ 0) : clearedNumerator z y z = reducedDensity z y := by
  have hZ : coordinateProduct z ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hz i)
  have hp : (∏ i, (-2:ℂ)/(z i-(z i)⁻¹)) =
      (coordinateProduct z)⁻¹ * ∏ i, residueFactor (z i) := by
    simp_rw [residueFactor_cleared (hz _)]
    simp only [Finset.prod_mul_distrib, coordinateProduct, Finset.prod_inv_distrib]
  have hc : (1+coordinateProduct z/coordinateProduct y)*(coordinateProduct z)⁻¹ =
      (coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹ := by
    field_simp
  unfold clearedNumerator reducedDensity
  rw [hp]
  calc
    _ = ((1+coordinateProduct z/coordinateProduct y)*(coordinateProduct z)⁻¹) /
      ((1-coordinateProduct z)*(1-coordinateProduct y)) *
      pairProduct z * pairProduct y * ∏ i, residueFactor (z i) := by ring
    _ = _ := by rw [hc]

end
end IsingBulk.First
