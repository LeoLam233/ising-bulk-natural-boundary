import IsingBulk.First.MeanCoordinateMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual mean/shape change of variables and Fubini, with its proved absolute
Jacobian one and the source mean coordinate integrated first. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory

theorem integral_meanShapeChart (n : ℕ) (f : (Fin (n+1) → ℝ) → ℂ) (hf : Integrable f) :
    (∫ x, f x) = ∫ t : Fin n → ℝ, ∫ v : ℝ, f (meanShapeChart v t) := by
  let e : (ℝ × (Fin n → ℝ)) ≃ᵐ (Fin (n+1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm _
  have he (p : ℝ × (Fin n → ℝ)) : e p = Fin.cons p.1 p.2 := by
    simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
  have heq (p : ℝ × (Fin n → ℝ)) : meanCoordinateMap n (e p) = meanShapeChart p.1 p.2 := by
    simp only [he,meanCoordinateMap,Fin.cons_zero,Fin.cons_succ]
  have hi := (meanCoordinateMap_measurePreserving n).integrable_comp_of_integrable hf
  have hi' := hem.integrable_comp_of_integrable hi
  have hit : Integrable (fun p : ℝ × (Fin n → ℝ) => f (meanShapeChart p.1 p.2))
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    simpa only [Function.comp_def,heq] using hi'
  calc
    _ = ∫ q, f (meanCoordinateMap n q) := (integral_meanCoordinateMap f hf.aestronglyMeasurable).symm
    _ = ∫ p : ℝ × (Fin n → ℝ), f (meanCoordinateMap n (e p)) := by
      rw [← hem.map_eq,integral_map_equiv]
    _ = ∫ p : ℝ × (Fin n → ℝ), f (meanShapeChart p.1 p.2) := by simp_rw [heq]
    _ = _ := by
      rw [Measure.volume_eq_prod]
      exact integral_prod_symm _ hit

end
end IsingBulk.First
