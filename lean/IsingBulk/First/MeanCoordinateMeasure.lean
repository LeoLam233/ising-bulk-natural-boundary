import IsingBulk.First.MeanJacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The mean-first coordinate map preserves the actual product Lebesgue
measure. This is the measure-level meaning of the source absolute Jacobian one. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory

 theorem meanChartMatrix_measurePreserving (n : ℕ) :
    MeasurePreserving (Matrix.toLin' (meanChartMatrix n)) volume volume := by
  have hn : (meanChartMatrix n).det ≠ 0 := by rw [meanChartMatrix_det]; exact pow_ne_zero _ (by norm_num)
  refine ⟨(Matrix.toLin' (meanChartMatrix n)).continuous_on_pi.measurable, ?_⟩
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hn
  simpa only [abs_inv, meanChartMatrix_abs_det, inv_one, ENNReal.ofReal_one, one_smul] using hm

def meanCoordinateMap (n : ℕ) (q : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  meanShapeChart (q 0) (fun j => q j.succ)

theorem meanCoordinateMap_eq_matrix (n : ℕ) :
    meanCoordinateMap n = Matrix.toLin' (meanChartMatrix n) := by
  funext q
  have he : Fin.cons (q 0) (fun j => q j.succ) = q := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  have hm := meanChartMatrix_mulVec n (q 0) (fun j => q j.succ)
  rw [he] at hm
  exact hm.symm

theorem meanCoordinateMap_measurePreserving (n : ℕ) :
    MeasurePreserving (meanCoordinateMap n) volume volume := by
  rw [meanCoordinateMap_eq_matrix]
  exact meanChartMatrix_measurePreserving n

/-- A genuine integral change of variables for the source mean/shape chart,
with no extra determinant factor. -/
theorem integral_meanCoordinateMap {n : ℕ} (f : (Fin (n+1) → ℝ) → ℂ)
    (hf : AEStronglyMeasurable f volume) :
    (∫ q, f (meanCoordinateMap n q)) = ∫ u, f u := by
  have hm := meanCoordinateMap_measurePreserving n
  have hfm : AEStronglyMeasurable f (Measure.map (meanCoordinateMap n) volume) := by
    rw [hm.map_eq]
    exact hf
  have he := integral_map hm.measurable.aemeasurable hfm
  rw [hm.map_eq] at he
  exact he.symm

end
end IsingBulk.First
