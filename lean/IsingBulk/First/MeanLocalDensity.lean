import IsingBulk.First.MeanYResidue
import IsingBulk.First.MeanPoleExclusion

/-! The actual reduced local angular density and its mean-residue numerator.
The N! factor and fixed shape weight remain outside the mean operation. -/
namespace IsingBulk.First
noncomputable section
open Complex Set
open scoped BigOperators

/-- Literal source lower-root tuple in the mean/shape chart. -/
def meanChartRoots {n : ℕ} (s : ℂ) (rho alpha : ℝ) (t : Fin n → ℝ) (v : ℂ) :
    Fin (n+1) → ℂ := fun j => phaseRoot
      (IsingBulk.Jets.chartW s rho alpha (((shapeExtend t j:ℝ):ℂ)+v/(n+1)))

/-- Every retained normalized y measure contributes y/(2*pi). -/
def meanAngularJacobian {n : ℕ} (rho alpha : ℝ) (t : Fin n → ℝ) (v : ℂ) : ℂ :=
  ∏ j, meanChartY rho alpha t v j / (2*(Real.pi:ℂ))

def meanLocalDensity {n : ℕ} (s : ℂ) (rho alpha : ℝ) (t : Fin n → ℝ) (v : ℂ) : ℂ :=
  reducedDensity (meanChartRoots s rho alpha t v) (meanChartY rho alpha t v) *
    meanAngularJacobian rho alpha t v

/-- Remove only the Y denominator from the actual source reduced density. -/
def meanLocalNumerator {n : ℕ} (s : ℂ) (rho alpha : ℝ) (t : Fin n → ℝ) (v : ℂ) : ℂ :=
  ((coordinateProduct (meanChartRoots s rho alpha t v))⁻¹ +
    (coordinateProduct (meanChartY rho alpha t v))⁻¹) /
    (1-coordinateProduct (meanChartRoots s rho alpha t v)) *
    pairProduct (meanChartRoots s rho alpha t v) * pairProduct (meanChartY rho alpha t v) *
    (∏ j, residueFactor (meanChartRoots s rho alpha t v j)) * meanAngularJacobian rho alpha t v

theorem meanLocalDensity_eq_Y_quotient {n : ℕ} (s : ℂ) (rho alpha : ℝ)
    (t : Fin n → ℝ) (v : ℂ) :
    meanLocalDensity s rho alpha t v =
      meanLocalNumerator s rho alpha t v / (1-meanProductY (n+1) rho alpha v) := by
  unfold meanLocalDensity meanLocalNumerator reducedDensity
  rw [coordinateProduct_meanChartY]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem meanLocalDensity_centered {n : ℕ} (s : ℂ) (rho alpha : ℝ)
    (t : Fin n → ℝ) (w : ℂ)
    (hroot : exp (-(n+1:ℂ)*(alpha:ℂ)*I) = 1) :
    meanLocalDensity s rho alpha t (physicalMeanPole (n+1) rho+w) =
      meanLocalNumerator s rho alpha t (physicalMeanPole (n+1) rho+w) /
        centeredMeanDenominator w := by
  rw [meanLocalDensity_eq_Y_quotient, meanProductY_translate_pole]
  · rfl
  · simpa using hroot

/-- The actual local hard-mean contour identity. The remaining premise is
ordinary differentiability of its explicitly defined numerator on the shifted
rectangle; all normalization, pole identification and orientation are proved. -/
theorem actual_mean_rectangle_residue {n : ℕ} (s : ℂ) (rho alpha delta height : ℝ)
    (t : Fin n → ℝ)
    (hroot : exp (-(n+1:ℂ)*(alpha:ℂ)*I) = 1)
    (hd : 0 < delta) (hdpi : delta < 2*Real.pi)
    (hrho : 0 < -(n+1:ℝ)*rho) (hheight : -(n+1:ℝ)*rho < height)
    (hf : DifferentiableOn ℂ
      (fun w => meanLocalNumerator s rho alpha t (physicalMeanPole (n+1) rho+w))
      (rectangleSet delta (-(n+1:ℝ)*rho) (-height+(-(n+1:ℝ)*rho)))) :
    clockwiseRectangle delta 0 (-height) (meanLocalDensity s rho alpha t) =
      2*(Real.pi:ℂ)*meanLocalNumerator s rho alpha t (physicalMeanPole (n+1) rho) := by
  let a : ℝ := -(n+1:ℝ)*rho
  let G : ℂ → ℂ := fun w => meanLocalDensity s rho alpha t (physicalMeanPole (n+1) rho+w)
  have hshift : (fun v : ℂ => G (v+(a:ℂ)*I)) = meanLocalDensity s rho alpha t := by
    funext v
    dsimp [G, a, physicalMeanPole]
    congr 1
    push_cast
    ring
  rw [← hshift, clockwiseRectangle_vertical_translate]
  have he : G = fun w =>
      meanLocalNumerator s rho alpha t (physicalMeanPole (n+1) rho+w)/centeredMeanDenominator w :=
    funext (fun w => meanLocalDensity_centered s rho alpha t w hroot)
  rw [he]
  have hres := clockwiseRectangle_centered_Y_residue hd hdpi hrho
    (show -height+a < 0 by dsimp [a]; linarith) hf
  simpa only [zero_add, add_zero] using! hres

end
end IsingBulk.First
