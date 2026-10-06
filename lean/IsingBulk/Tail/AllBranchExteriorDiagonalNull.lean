import IsingBulk.Tail.CoordinateDifferenceJets
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace IsingBulk.Tail
noncomputable section
open MeasureTheory

theorem allBranchExterior_coordinate_diagonal_null {N : ℕ} (p q : Fin N) (hpq : p ≠ q) :
    volume {u : Fin N → ℝ | u p=u q}=0 := by
  let L : (Fin N → ℝ) →L[ℝ] ℝ := coordinateDifference p q
  have hproper : L.toLinearMap.ker ≠ ⊤ := by
    intro he
    have hm : (Pi.single p (1:ℝ)) ∈ L.toLinearMap.ker := by rw [he]; trivial
    have hz : L (Pi.single p (1:ℝ))=0 := hm
    simp [L,coordinateDifference,Ne.symm hpq] at hz
  have hh := Measure.addHaar_submodule (volume : Measure (Fin N → ℝ)) L.toLinearMap.ker hproper
  have he : {u : Fin N → ℝ | u p=u q}=(L.toLinearMap.ker : Set (Fin N → ℝ)) := by
    ext u
    simp [L,coordinateDifference,LinearMap.mem_ker,sub_eq_zero]
  rw [he]
  exact hh

theorem allBranchExterior_ae_selected_distinct {N : ℕ} (p q : Fin N) (hpq : p ≠ q) :
    ∀ᵐ u : Fin N → ℝ, u p ≠ u q := by
  rw [ae_iff]
  simpa only [not_not] using allBranchExterior_coordinate_diagonal_null p q hpq

end
end IsingBulk.Tail
