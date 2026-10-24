import IsingBulk.Anisotropic.Final.IsotropicLocal
import IsingBulk.Anisotropic.Geometry.IsotropicBoundary
import IsingBulk.Anisotropic.Geometry.IsotropicDensity

namespace IsingBulk.Anisotropic
noncomputable section
open Set

theorem isotropic_high_noncritical_boundary {z : ℂ} (hz : z ∈ frontier (omegaH 1))
    (hc : Complex.cosh z ≠ 0) :
    ¬ HasDomainExtension (omegaH 1) isotropicHighPullback z :=
  isotropic_high_no_extension_in_strip (frontier_omegaH_one_norm hz) hc
    (frontier_omegaH_one_noncritical_im hz hc)

theorem isotropic_low_noncritical_boundary {z : ℂ} (hz : z ∈ frontier (omegaL 1))
    (hc : Complex.cosh z ≠ 0) :
    ¬ HasDomainExtension (omegaL 1) isotropicLowPullback z :=
  isotropic_low_no_extension_right (frontier_omegaL_one_norm hz) hc
    (frontier_omegaL_one_noncritical_re hz hc)

/-- Entire isotropic high-temperature boundary, including its critical tips. -/
theorem isotropic_high_naturalBoundary :
    NaturalBoundaryOn (omegaH 1) isotropicHighPullback :=
  naturalBoundaryOn_of_dense_obstructions isotropicHighPullback_analyticOn_omega
    frontier_omegaH_one_subset_closure_noncritical
    (fun _ hz => isotropic_high_noncritical_boundary hz.1 hz.2)

/-- Entire isotropic low-temperature boundary on the right half-plane cover. -/
theorem isotropic_low_naturalBoundary :
    NaturalBoundaryOn (omegaL 1) isotropicLowPullback :=
  naturalBoundaryOn_of_dense_obstructions isotropicLowPullback_analyticOn_omega
    frontier_omegaL_one_subset_closure_noncritical
    (fun _ hz => isotropic_low_noncritical_boundary hz.1 hz.2)

end
end IsingBulk.Anisotropic
