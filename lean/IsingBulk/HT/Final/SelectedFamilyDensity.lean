import IsingBulk.HT.Final.DenseBoundary
import IsingBulk.HT.First.NegativePrimeDensity

/-! Density of the two original integer-angle prime families. The negative
family is not obtained by reflecting the positive one. Endpoint closure also
includes the imaginary-axis point, where neither open family is admissible. -/
namespace IsingBulk.HT.Final
noncomputable section
open Set IsingBulk.Final IsingBulk.HT.First
open scoped Topology

def originalSelectedFamily : Set ℂ :=
  IsingBulk.PrimeFamily.selectedFamily ∪ negativeSelectedFamily

theorem negativeSelectedFamily_dense_closed_arc {t : ℝ}
    (ht : Real.pi/2 ≤ t) (htpi : t ≤ Real.pi) :
    unitAngle t ∈ closure negativeSelectedFamily := by
  have hI : t ∈ closure (Ioo (Real.pi/2) Real.pi) := by
    rw [closure_Ioo (by linarith [Real.pi_pos] : Real.pi/2 ≠ Real.pi)]
    exact ⟨ht,htpi⟩
  have hi := image_closure_subset_closure_image unitAngle_continuous
    (mem_image_of_mem unitAngle hI)
  apply (closure_minimal (s := unitAngle '' Ioo (Real.pi/2) Real.pi)
    ?_ isClosed_closure) hi
  rintro _ ⟨u,hu,rfl⟩
  exact negativeSelectedFamily_dense_arc hu.1 hu.2

/-- The actual two families cover the full upper boundary by closure, including
both real endpoints and the imaginary-axis endpoint. -/
theorem originalSelectedFamily_dense_closed_upper_arc {t : ℝ}
    (ht : 0 ≤ t) (htpi : t ≤ Real.pi) :
    unitAngle t ∈ closure originalSelectedFamily := by
  by_cases hm : t ≤ Real.pi/2
  · exact closure_mono (by intro z hz; exact Or.inl hz)
      (IsingBulk.Final.selectedFamily_dense_closed_arc ht hm)
  · exact closure_mono (by intro z hz; exact Or.inr hz)
      (negativeSelectedFamily_dense_closed_arc (le_of_lt (lt_of_not_ge hm)) htpi)

end
end IsingBulk.HT.Final
