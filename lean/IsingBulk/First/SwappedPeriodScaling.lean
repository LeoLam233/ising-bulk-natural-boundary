import IsingBulk.First.ShapePeriodTheorem

/-! An exact constrained-integral scaling for the swapped ordered chart.
It proves coefficient equality without making a branch-choice comparison by hand. -/
namespace IsingBulk.First
noncomputable section
open Complex MeasureTheory

 theorem shapePeriod_weighted_scaling (n k : ℕ) (Q : ℝ) (c : ℂ)
    {r : ℝ} (hr : 0 < r) :
    (r:ℂ)^((n+1)^2+k) * shapePeriod n k (r*Q) ((r:ℂ)^3*c) =
      shapePeriod n k Q c := by
  let f : ShapeSpace n → ℂ := fun x =>
    (shapeVandermondeSq x:ℂ) / ((Q:ℂ)+c*(‖x‖:ℂ)^2)^(k+1)
  let g : ShapeSpace n → ℂ := fun x =>
    (shapeVandermondeSq x:ℂ) / (((r*Q:ℝ):ℂ)+(r:ℂ)^3*c*(‖x‖:ℂ)^2)^(k+1)
  have hrC : (r:ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hpoint (x : ShapeSpace n) : (r:ℂ)^((n+1)^2+k) * g x =
      (r:ℂ)^n * f (r • x) := by
    dsimp [f,g]
    rw [shapeVandermondeSq_homogeneous, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow]
    have he : (n+1)^2+k = n+(n+1)*n+(k+1) := by ring
    have hd : (r:ℂ)*(Q:ℂ)+(r:ℂ)^3*c*(‖x.1‖:ℂ)^2 =
        (r:ℂ)*((Q:ℂ)+c*((r:ℂ)*(‖x.1‖:ℂ))^2) := by ring
    rw [hd, he, pow_add, mul_pow]
    field_simp
    ring
  have hchange : (r:ℂ)^n * (∫ x : ShapeSpace n, f (r • x)) = ∫ x : ShapeSpace n, f x := by
    have h := (volume : Measure (ShapeSpace n)).integral_comp_smul_of_nonneg f r (hR := hr.le)
    rw [finrank_shapeSpace] at h
    rw [h]
    simp only [Complex.real_smul, ofReal_inv, ofReal_pow]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hrC), one_mul]
  have hi : (r:ℂ)^((n+1)^2+k) * (∫ x : ShapeSpace n, g x) = ∫ x : ShapeSpace n, f x := by
    rw [← integral_const_mul, ← hchange, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  rw [shapePeriod_eq_intrinsic,shapePeriod_eq_intrinsic]
  change (r:ℂ)^((n+1)^2+k) * ((Real.sqrt (n+1))⁻¹ • (∫ x : ShapeSpace n, g x)) =
    (Real.sqrt (n+1))⁻¹ • (∫ x : ShapeSpace n, f x)
  simp only [Complex.real_smul]
  linear_combination ((Real.sqrt (n+1))⁻¹:ℝ) * hi

end
end IsingBulk.First
