import IsingBulk.First.SourceAngularPeriodicity
import IsingBulk.First.GlobalRootChartBridge
import IsingBulk.First.MeanLocalDensity

/-! Exact identification of the reduced source angular density in the real
mean/shape chart, retaining every normalized remaining y measure. -/
namespace IsingBulk.First
noncomputable section
open Complex
open scoped BigOperators

theorem meanChartY_eq_angleTuple {n : ℕ} (rho alpha v : ℝ) (t : Fin n → ℝ) :
    meanChartY rho alpha t (v:ℂ) =
      angleTuple (Real.exp rho) (fun j => meanShapeChart v t j-alpha) := by
  funext j
  unfold meanChartY IsingBulk.Jets.angularY angleTuple anglePoint circleMap meanShapeChart
  simp only [zero_add,Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem meanChartRoots_eq_globalRoot {n : ℕ} (s : ℂ) (rho alpha : ℝ)
    (t : Fin n → ℝ) (v : ℂ) :
    meanChartRoots s rho alpha t v = fun j => globalRoot s (meanChartY rho alpha t v j) := by
  funext j
  rw [meanChartRoots,phaseRoot_eq_inverse]
  rfl

theorem meanAngularJacobian_eq_angleProduct {n : ℕ} (rho alpha v : ℝ) (t : Fin n → ℝ) :
    meanAngularJacobian rho alpha t (v:ℂ) =
      angleProductJacobian (Real.exp rho) (fun j => meanShapeChart v t j-alpha) := by
  unfold meanAngularJacobian angleProductJacobian angleJacobian
  rw [meanChartY_eq_angleTuple]
  rfl

theorem sourceReducedAngularDensity_meanShape {n : ℕ} (s : ℂ) (rho alpha v : ℝ) (t : Fin n → ℝ) :
    sourceReducedAngularDensity (Real.exp rho) s (fun j => meanShapeChart v t j-alpha) =
      meanLocalDensity s rho alpha t (v:ℂ) := by
  unfold sourceReducedAngularDensity meanLocalDensity
  rw [meanChartRoots_eq_globalRoot,meanChartY_eq_angleTuple,meanAngularJacobian_eq_angleProduct]
  unfold angleTuple
  ring

end
end IsingBulk.First
