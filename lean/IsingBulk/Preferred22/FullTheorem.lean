import IsingBulk.Preferred22.ActualCoefficientTail
import IsingBulk.Preferred22.ActualFiniteComplement
import IsingBulk.Preferred22.ActualFirstSingularity
import IsingBulk.Preferred22.JointSiteSummability
import IsingBulk.Preferred22.PrimeBranchData

/-! The complete Preferred22 proof chain. Each selected-point first,
finite-complement and infinite absolute-tail obligation is supplied by
the actual new physical-source estimates before the final assembly. -/
namespace IsingBulk.Preferred22
noncomputable section

theorem preferred_selected_analytic_obligations : PreferredSelectedAnalyticObligations := by
  intro p hp hp5 a ha
  refine ⟨preferred_actual_first_singularity hp hp5 ha,?_,?_⟩
  · exact preferred_actual_finite_complement (preferredPrimeBranchData ha) hp hp5 ha rfl
      ((2*p)^2/2-1)
  · exact preferred_actual_absolute_tail (preferredPrimeBranchData ha) hp ha rfl
      (2*p) ((2*p)^2/2-1) (by omega) ⟨p,by omega⟩ (preferred_prime_critical_derivative hp.pos)

/-- Complete connected low-temperature bulk susceptibility, both pure
phases, all sites including the origin, every positive even order and its
actual infinite sum, physical branches and the entire unit circle. The
only physical input interfaces are the scoped PT and Yang identities
already quantified inside the exact target. -/
theorem preferred_full_target : PreferredFullTarget :=
  preferredFullTarget_of_selected_obligations preferred_selected_analytic_obligations

theorem preferred_bulk_natural_boundary :
    ∀ ζ : ℂ,‖ζ‖=1 → ¬HasExteriorExtension bulkFunction ζ :=
  bulkFunction_boundary_of_selected_obligations preferred_selected_analytic_obligations

theorem preferred_physical_bulk_natural_boundary (J : ℝ) (hJ : 0<J) :
    ∀ ζ : ℂ,‖ζ‖=1 → ¬HasPhysicalBoundaryExtension J bulkFunction ζ :=
  physical_bulk_boundary_of_selected_obligations preferred_selected_analytic_obligations hJ

end
end IsingBulk.Preferred22
