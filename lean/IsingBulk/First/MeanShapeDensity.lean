import IsingBulk.First.MeanLocalDensity
import IsingBulk.First.ResidueBranch

/-! The actual post-mean-residue shape density. The contour radius disappears
from this literal source expression before s differentiation or shape rescaling. -/
namespace IsingBulk.First
noncomputable section
open Complex
open scoped BigOperators

def shapeY {n : ℕ} (alpha : ℝ) (t : Fin n → ℝ) : Fin (n+1) → ℂ :=
  fun j => exp ((((shapeExtend t j:ℝ):ℂ)-(alpha:ℂ))*I)

def shapeZ {n : ℕ} (s : ℂ) (alpha : ℝ) (t : Fin n → ℝ) : Fin (n+1) → ℂ :=
  fun j => phaseRoot (sourceW s (shapeY alpha t j))

def shapeZProduct {n : ℕ} (s : ℂ) (alpha : ℝ) (t : Fin n → ℝ) : ℂ :=
  coordinateProduct (shapeZ s alpha t)

def shapePoleDenominator {n : ℕ} (s : ℂ) (alpha : ℝ) (t : Fin n → ℝ) : ℂ :=
  1-shapeZProduct s alpha t

/-- The remaining regular numerator, including all normalized y measures.
The fixed factor 1/N! and fixed shape cutoff are kept outside. -/
def shapeRegularNumerator {n : ℕ} (s : ℂ) (alpha : ℝ) (t : Fin n → ℝ) : ℂ :=
  ((shapeZProduct s alpha t)⁻¹+1) * pairProduct (shapeZ s alpha t) * pairProduct (shapeY alpha t) *
    (∏ j, residueFactor (shapeZ s alpha t j)) * (∏ j, shapeY alpha t j/(2*(Real.pi:ℂ)))

def postMeanDensity {n : ℕ} (s : ℂ) (alpha : ℝ) (t : Fin n → ℝ) : ℂ :=
  2*(Real.pi:ℂ)*shapeRegularNumerator s alpha t/shapePoleDenominator s alpha t

theorem meanChartY_at_pole_eq_shapeY {n : ℕ} (rho alpha : ℝ) (t : Fin n → ℝ) :
    meanChartY rho alpha t (physicalMeanPole (n+1) rho) = shapeY alpha t := by
  funext j
  exact meanChartY_at_physicalMeanPole rho alpha t j

theorem meanChartRoots_at_pole_eq_shapeZ {n : ℕ} (s : ℂ) (rho alpha : ℝ) (t : Fin n → ℝ) :
    meanChartRoots s rho alpha t (physicalMeanPole (n+1) rho) = shapeZ s alpha t := by
  funext j
  change phaseRoot (IsingBulk.Branch.dispersion s
    (meanChartY rho alpha t (physicalMeanPole (n+1) rho) j)) = _
  rw [meanChartY_at_pole_eq_shapeY]
  rfl

theorem coordinateProduct_shapeY {n : ℕ} (alpha : ℝ) (t : Fin n → ℝ)
    (hroot : exp (-(n+1:ℂ)*(alpha:ℂ)*I) = 1) : coordinateProduct (shapeY alpha t) = 1 := by
  rw [← meanChartY_at_pole_eq_shapeY (0:ℝ) alpha t, coordinateProduct_meanChartY]
  apply meanProductY_at_physicalMeanPole
  simpa using hroot

/-- Exact identification of the physical residue numerator with its radius-free
shape expression; this is not an asymptotic model. -/
theorem meanLocalNumerator_at_pole {n : ℕ} (s : ℂ) (rho alpha : ℝ) (t : Fin n → ℝ)
    (hroot : exp (-(n+1:ℂ)*(alpha:ℂ)*I) = 1) :
    meanLocalNumerator s rho alpha t (physicalMeanPole (n+1) rho) =
      shapeRegularNumerator s alpha t/shapePoleDenominator s alpha t := by
  unfold meanLocalNumerator meanAngularJacobian
  rw [meanChartRoots_at_pole_eq_shapeZ, meanChartY_at_pole_eq_shapeY,
    coordinateProduct_shapeY alpha t hroot]
  unfold shapeRegularNumerator shapePoleDenominator shapeZProduct
  simp only [inv_one, div_eq_mul_inv]
  ring

theorem postMeanDensity_eq_physical_residue {n : ℕ} (s : ℂ) (rho alpha : ℝ) (t : Fin n → ℝ)
    (hroot : exp (-(n+1:ℂ)*(alpha:ℂ)*I) = 1) :
    2*(Real.pi:ℂ)*meanLocalNumerator s rho alpha t (physicalMeanPole (n+1) rho) =
      postMeanDensity s alpha t := by
  rw [meanLocalNumerator_at_pole s rho alpha t hroot]
  unfold postMeanDensity
  ring

end
end IsingBulk.First
