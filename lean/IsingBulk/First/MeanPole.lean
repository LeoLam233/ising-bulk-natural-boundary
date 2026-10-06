import IsingBulk.First.MeanCoordinates
import IsingBulk.First.ContourDefinitions
import IsingBulk.Analysis.JetsChart

/-! The literal Y product and its physical pole in the mean coordinate.
The contour orientation identity is deliberately separate from these exact
algebraic and derivative facts. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

/-- Fixed logarithmic radius rho; v is the complexified angular sum. -/
def meanChartY {n : ℕ} (rho alpha : ℝ) (t : Fin n → ℝ) (v : ℂ) : Fin (n+1) → ℂ :=
  fun j => IsingBulk.Jets.angularY rho alpha
    ((shapeExtend t j : ℝ) + v / (n+1))

/-- The single source product denominator after collecting zero-sum shapes. -/
def meanProductY (N : ℕ) (rho alpha : ℝ) (v : ℂ) : ℂ :=
  Complex.exp ((N:ℂ) * ((rho:ℂ) - (alpha:ℂ)*Complex.I) + v*Complex.I)

def physicalMeanPole (N : ℕ) (rho : ℝ) : ℂ := (N:ℂ)*(rho:ℂ)*Complex.I

theorem coordinateProduct_meanChartY {n : ℕ} (rho alpha : ℝ)
    (t : Fin n → ℝ) (v : ℂ) :
    coordinateProduct (meanChartY rho alpha t v) = meanProductY (n+1) rho alpha v := by
  unfold meanProductY
  simp only [coordinateProduct, meanChartY, IsingBulk.Jets.angularY]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hz : ∑ j : Fin (n+1), ((shapeExtend t j : ℝ) : ℂ) = 0 := by
    exact_mod_cast sum_shapeExtend t
  rw [hz]
  push_cast
  have hN : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp
  ring

theorem meanChartY_at_physicalMeanPole {n : ℕ} (rho alpha : ℝ)
    (t : Fin n → ℝ) (j : Fin (n+1)) :
    meanChartY rho alpha t (physicalMeanPole (n+1) rho) j =
      Complex.exp (((shapeExtend t j : ℝ) - (alpha:ℂ))*Complex.I) := by
  unfold meanChartY physicalMeanPole IsingBulk.Jets.angularY
  congr 1
  push_cast
  have hN : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp
  ring_nf
  simp [Complex.I_sq]

theorem meanProductY_at_physicalMeanPole (N : ℕ) (rho alpha : ℝ)
    (hroot : Complex.exp (-(N:ℂ)*(alpha:ℂ)*Complex.I) = 1) :
    meanProductY N rho alpha (physicalMeanPole N rho) = 1 := by
  unfold meanProductY physicalMeanPole
  convert hroot using 1
  congr 1
  ring_nf
  simp [Complex.I_sq]

theorem meanProductY_hasDerivAt (N : ℕ) (rho alpha : ℝ) (v : ℂ) :
    HasDerivAt (meanProductY N rho alpha) (Complex.I * meanProductY N rho alpha v) v := by
  unfold meanProductY
  convert ((((hasDerivAt_id v).mul_const Complex.I).const_add
    ((N:ℂ)*((rho:ℂ)-(alpha:ℂ)*Complex.I))).cexp) using 1 <;> simp [id_eq, mul_comm]

/-- Exact denominator derivative at the crossed physical pole. -/
theorem one_sub_meanProductY_pole_derivative (N : ℕ) (rho alpha : ℝ)
    (hroot : Complex.exp (-(N:ℂ)*(alpha:ℂ)*Complex.I) = 1) :
    HasDerivAt (fun v => 1 - meanProductY N rho alpha v) (-Complex.I)
      (physicalMeanPole N rho) := by
  simpa [meanProductY_at_physicalMeanPole N rho alpha hroot] using
    (meanProductY_hasDerivAt N rho alpha (physicalMeanPole N rho)).const_sub 1

/-- The scalar sign calculation, to be used only after proving the actual
clockwise rectangle integral. This is not a residue theorem on its own. -/
theorem clockwise_mean_residue_coefficient :
    (-2 * (Real.pi:ℂ) * Complex.I) / (-Complex.I) = 2 * (Real.pi:ℂ) := by
  field_simp

end
end IsingBulk.First
