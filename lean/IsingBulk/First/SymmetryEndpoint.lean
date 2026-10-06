import IsingBulk.First.BulkSymmetry
import IsingBulk.First.ResidueAdmissibility

/-! Physical symmetry transfer with the actual admissible contour and explicitly
identified convergent bulk representation. Exterior contour existence is separate. -/
namespace IsingBulk.First
noncomputable section
open Set

/-- The representation input contains only the actual source expansion and its
convergence on admissible contours. Both symmetry conclusions are constructed. -/
theorem lemma_symmetry_admissible (χ : ℂ → ℂ) (r : ℝ) (s : ℂ) (z : ℂ → ℂ)
    (hs : 1 < ‖s‖) (h : ScalarResidueAdmissible r s z)
    (hphysical : ∀ (t : ℂ) (q : ℂ → ℂ), 1 < ‖t‖ → ScalarResidueAdmissible r t q →
      Summable (fun n : ℕ => doubleFormFactor (2*(n+1)) r t) ∧ χ t = normalizedBulkSeries r t) :
    (χ (-s) = χ s ∧ χ (star s) = star (χ s)) ∧
    ∀ N : ℕ, Even N →
      doubleFormFactor N r (-s) = doubleFormFactor N r s ∧
      doubleFormFactor N r (star s) = star (doubleFormFactor N r s) := by
  have hp := hphysical s z hs h
  have hn := hphysical (-s) (fun y => -z (-y)) (by simpa using hs) h.neg
  have hc := hphysical (star s) (fun y => star (z (star y))) (by simpa using hs) h.conjugate
  refine ⟨susceptibility_symmetry_of_representation χ r s hs hp.2 hn.2 hc.2 ?_, ?_⟩
  · intro t ht
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact hp.1
    · exact hn.1
    · exact hc.1
  · intro N hN
    exact ⟨doubleFormFactor_even N hN r s, doubleFormFactor_conjugate N r s⟩

end
end IsingBulk.First
