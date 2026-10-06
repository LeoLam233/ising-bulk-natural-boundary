import IsingBulk.First.ShapeDominatedLimit
import IsingBulk.First.ShapeLowerOrders

/-! Fixed-radius, parameter-independent bounds for post-mean lower pole orders. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Metric

theorem shapeVandermondeSq_zero {n : ℕ} (hn : 1 ≤ n) :
    shapeVandermondeSq (0 : ShapeSpace n) = 0 := by
  unfold shapeVandermondeSq firstVandermonde
  have hp : (0, Fin.last n) ∈ firstStrictPairs (n+1) := by
    rw [mem_firstStrictPairs]
    change 0 < n
    omega
  have hz : (∏ p ∈ firstStrictPairs (n+1),
      ((0 : ShapeSpace n).1 p.1 - (0 : ShapeSpace n).1 p.2)) = 0 :=
    Finset.prod_eq_zero hp (by simp)
  rw [hz, zero_pow (by decide)]

theorem norm_lower_shapeQuotient_le {n j : ℕ} (hn : 1 ≤ n) {M c : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (A D : ShapeSpace n → ℂ)
    (hA : ∀ x, ‖A x‖ ≤ M)
    (hD : ∀ x, A x ≠ 0 → c*‖x‖^2 ≤ ‖D x‖) (x : ShapeSpace n) :
    ‖localShapeQuotient j A D x‖ ≤
      (M/c^(j+1))*(shapeVandermondeSq x/‖x‖^(2*(j+1))) := by
  by_cases hx : x = 0
  · subst x
    simp [localShapeQuotient, shapeVandermondeSq_zero hn]
  by_cases ha : A x = 0
  · simp only [localShapeQuotient, ha, mul_zero, zero_div, norm_zero]
    exact mul_nonneg (div_nonneg hM (pow_nonneg hc.le _))
      (div_nonneg (shapeVandermondeSq_nonneg x) (by positivity))
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hpoly := shapeVandermondeSq_nonneg x
  rw [localShapeQuotient, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hpoly, norm_pow]
  calc
    shapeVandermondeSq x * ‖A x‖ / ‖D x‖^(j+1)
        ≤ shapeVandermondeSq x * M / (c*‖x‖^2)^(j+1) := by
      calc
        _ ≤ shapeVandermondeSq x * M / ‖D x‖^(j+1) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hA x) hpoly) (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hpoly hM) (by positivity)
          (pow_le_pow_left₀ (by positivity) (hD x ha) _)
    _ = (M/c^(j+1))*(shapeVandermondeSq x/‖x‖^(2*(j+1))) := by
      simp only [mul_pow, pow_mul, div_eq_mul_inv, mul_inv_rev]
      ring

/-- A uniform bound on the integral over a fixed shape ball. Its right-hand
side contains no radial parameter; source amplitude/gap hypotheses are explicit. -/
theorem localShapeQuotient_lower_bound {n k j : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) (hj : j < k) (R : ℝ) {M c : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) (A D : ShapeSpace n → ℂ)
    (hAmeas : Measurable A) (hDmeas : Measurable D)
    (hA : ∀ x, ‖A x‖ ≤ M)
    (hD : ∀ x, A x ≠ 0 → c*‖x‖^2 ≤ ‖D x‖) :
    IntegrableOn (localShapeQuotient j A D) (ball 0 R) ∧
    ‖∫ x : ShapeSpace n in ball 0 R, localShapeQuotient j A D x‖ ≤
      (M/c^(j+1)) * ∫ x : ShapeSpace n in ball 0 R,
        shapeVandermondeSq x/‖x‖^(2*(j+1)) := by
  have hi := (shape_lower_order_integrableOn hn hdegree hj R).const_mul (M/c^(j+1))
  have hm : Measurable (localShapeQuotient j A D) := by
    unfold localShapeQuotient
    exact ((Complex.continuous_ofReal.measurable.comp
      (shapeVandermondeSq_continuous n).measurable).mul hAmeas).div (hDmeas.pow_const _)
  have hb : ∀ᵐ x : ShapeSpace n ∂volume.restrict (ball 0 R),
      ‖localShapeQuotient j A D x‖ ≤
        (M/c^(j+1))*(shapeVandermondeSq x/‖x‖^(2*(j+1))) :=
    Filter.Eventually.of_forall (norm_lower_shapeQuotient_le (j := j) hn hM hc A D hA hD)
  have hf : IntegrableOn (localShapeQuotient j A D) (ball 0 R) :=
    hi.mono' hm.aestronglyMeasurable.restrict hb
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ x : ShapeSpace n in ball 0 R, ‖localShapeQuotient j A D x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ShapeSpace n in ball 0 R,
        (M/c^(j+1))*(shapeVandermondeSq x/‖x‖^(2*(j+1))) := integral_mono_ae hf.norm hi hb
    _ = _ := integral_const_mul _ _

end
end IsingBulk.First
