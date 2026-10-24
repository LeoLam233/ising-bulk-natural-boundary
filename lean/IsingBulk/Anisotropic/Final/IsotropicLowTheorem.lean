import IsingBulk.Anisotropic.Final.IsotropicLowReal
import IsingBulk.Anisotropic.Final.RealIntervalUniqueness
import IsingBulk.Anisotropic.Final.ActualHolomorphy
import IsingBulk.Anisotropic.Final.IsotropicBoundary

namespace IsingBulk.Anisotropic
noncomputable section
open Set FormFactors

theorem lowNormalizedBulk_one_eqOn {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors 1 corrH corrL) :
    EqOn (lowNormalizedBulk 1) isotropicLowPullback (omegaL 1) := by
  apply analytic_eqOn_of_real_interval (lowNormalizedBulk_analyticOnNhd (by norm_num))
    isotropicLowPullback_analyticOn_omega
    (omegaL_isSimplyConnected (by norm_num)).isPathConnected.isConnected.isPreconnected
    (a := criticalPoint 1+1) (b := criticalPoint 1+2) (by linarith)
  · intro x hx
    exact (real_mem_omegaL_iff (by norm_num) x).mpr (by linarith [hx.1])
  · intro x hx
    simpa [isotropicLowPullback,← Complex.ofReal_sinh] using
      isotropic_low_real_eq (by linarith [hx.1]) hphys

/-- Full actual isotropic LT connected sum. The sole physical premise supplies
its real onsite spin normalization, not a complex continuation assertion. -/
theorem lowNormalizedBulk_one_naturalBoundary {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors 1 corrH corrL) :
    NaturalBoundaryOn (omegaL 1) (lowNormalizedBulk 1) := by
  refine ⟨lowNormalizedBulk_analyticOnNhd (by norm_num),?_⟩
  intro z hz
  exact no_domain_extension_of_eqOn (lowNormalizedBulk_one_eqOn hphys).symm
    (isotropic_low_naturalBoundary.2 z hz)

end
end IsingBulk.Anisotropic
