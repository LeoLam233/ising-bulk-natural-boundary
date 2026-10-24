import IsingBulk.Anisotropic.Geometry.PerfectSpectrum
import Mathlib.Topology.Connected.LocallyConnected

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

/-- A component of an open planar set has no new boundary inside that set. -/
theorem frontier_connectedComponentIn_subset_compl {U : Set ℂ} (hU : IsOpen U) (a : ℂ) :
    frontier (connectedComponentIn U a)⊆Uᶜ := by
  intro z hz hzU
  rcases Metric.isOpen_iff.mp hU z hzU with ⟨r,hr,hrU⟩
  rcases mem_closure_iff.mp (frontier_subset_closure hz) _ Metric.isOpen_ball
    (Metric.mem_ball_self hr) with ⟨w,hwb,hwc⟩
  have hball : Metric.ball z r⊆connectedComponentIn U w :=
    Metric.isPreconnected_ball.subset_connectedComponentIn hwb hrU
  have he := connectedComponentIn_eq hwc
  have hzc : z∈connectedComponentIn U a := by
    rw [he]
    exact hball (Metric.mem_ball_self hr)
  rw [hU.connectedComponentIn.frontier_eq] at hz
  exact hz.2 hzc

theorem frontier_spectral_component_subset_spectralSet (lam : ℝ) (a : ℂ) :
    frontier (connectedComponentIn (spectralSet lam)ᶜ a)⊆spectralSet lam := by
  simpa only [compl_compl] using
    frontier_connectedComponentIn_subset_compl (spectralSet_isClosed lam).isOpen_compl a

theorem frontier_spectral_component_preperfect {lam : ℝ} (hlam : 0<lam) (a : ℂ) :
    Preperfect (frontier (connectedComponentIn (spectralSet lam)ᶜ a)) :=
  frontier_preperfect_of_ambient_preperfect (spectralSet_preperfect hlam)
    (spectralSet_isClosed lam).isOpen_compl.connectedComponentIn
    (connectedComponentIn_subset _ _) (frontier_spectral_component_subset_spectralSet lam a)

/-- Regular edges are dense on the boundary of every spectral-complement component. -/
theorem frontier_spectral_component_subset_closure_regular {lam : ℝ} (hlam : 0<lam)
    (hne : lam≠1) (a : ℂ) :
    frontier (connectedComponentIn (spectralSet lam)ᶜ a) ⊆
      closure {z | z∈frontier (connectedComponentIn (spectralSet lam)ᶜ a) ∧ RegularEdgePoint lam z} := by
  apply Set.Subset.trans (Preperfect.subset_closure_diff_locallyFinite (frontier_spectral_component_preperfect hlam a)
    (edgeExceptionalSet_locally_finite hlam hne))
  apply closure_mono
  intro z hz
  refine ⟨hz.1,regularEdgePoint_of_spectral_boundary
    (frontier_spectral_component_subset_spectralSet lam a hz.1) ?_ hz.2⟩
  exact frontier_not_mem_interior_of_subset_compl (connectedComponentIn_subset _ _) hz.1

end
end IsingBulk.Anisotropic
