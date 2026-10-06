import IsingBulk.Tail.MicrocoreLieIntegralBound
import IsingBulk.Tail.MicrocoreIntegralRegularity

/-! The product restricted arclength domain is exactly the fixed real
microcore cube used by the compact-support Lie theorem. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie MeasureTheory Set

def microcoreCube (N : ℕ) (b : ℝ) : Set (Fin N → ℝ) :=
  Icc (fun _ => -b) (fun _ => b)

theorem mem_microcoreCube {N : ℕ} (b : ℝ) (u : Fin N → ℝ) :
    u ∈ microcoreCube N b ↔ ∀ i, |u i| ≤ b := by
  simp only [microcoreCube,mem_Icc,Pi.le_def]
  exact ⟨fun h i => abs_le.mpr ⟨h.1 i,h.2 i⟩,
    fun h => ⟨fun i => (abs_le.mp (h i)).1,fun i => (abs_le.mp (h i)).2⟩⟩

theorem microcoreCube_compact (N : ℕ) (b : ℝ) : IsCompact (microcoreCube N b) := isCompact_Icc

theorem microcoreCoreMeasure_eq (N : ℕ) (b : ℝ) :
    microcoreCoreMeasure N b=volume.restrict (microcoreCube N b) := by
  rw [microcoreCoreMeasure,volume_pi,microcoreCube,← pi_univ_Icc]
  exact (Measure.restrict_pi_pi _ _).symm

theorem scaledMicroCutoff_tsupport_cube (N : ℕ) (b : ℝ) (hb : 0 < b) :
    tsupport (scaledMicroCutoff N b) ⊆ microcoreCube N b := by
  intro u hu
  apply (mem_microcoreCube b u).mpr
  exact scaledMicroCutoff_jet_tsupport hb [] hu

theorem microcore_integral_core_eq_full {N : ℕ} (b : ℝ) (f : (Fin N → ℝ) → ℂ)
    (hf : Function.support f ⊆ microcoreCube N b) :
    (∫ u, f u ∂microcoreCoreMeasure N b)=∫ u, f u := by
  rw [microcoreCoreMeasure_eq]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  by_contra hn
  exact hu (hf hn)

end
end IsingBulk.Tail
