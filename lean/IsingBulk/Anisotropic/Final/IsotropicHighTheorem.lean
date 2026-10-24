import IsingBulk.Anisotropic.Final.IsotropicHighReal
import IsingBulk.Anisotropic.Final.RealIntervalUniqueness
import IsingBulk.Anisotropic.Final.ActualHolomorphy
import IsingBulk.Anisotropic.Final.IsotropicBoundary

namespace IsingBulk.Anisotropic
noncomputable section
open Set

theorem highNormalizedBulk_one_eqOn :
    EqOn (FormFactors.highNormalizedBulk 1) isotropicHighPullback (omegaH 1) := by
  apply analytic_eqOn_of_real_interval (highNormalizedBulk_analyticOnNhd (by norm_num))
    isotropicHighPullback_analyticOn_omega
    (omegaH_isSimplyConnected (by norm_num)).isPathConnected.isConnected.isPreconnected
    (criticalPoint_pos (by norm_num : (0:ℝ)<1))
  · intro x hx
    exact real_mem_omegaH_of_nonneg_lt_critical (by norm_num) hx.1.le hx.2
  · intro x hx
    simpa [isotropicHighPullback,← Complex.ofReal_sinh] using isotropic_high_real_eq hx.1 hx.2

/-- Full actual isotropic high-temperature sum, not a proxy pullback. -/
theorem highNormalizedBulk_one_naturalBoundary :
    NaturalBoundaryOn (omegaH 1) (FormFactors.highNormalizedBulk 1) := by
  refine ⟨highNormalizedBulk_analyticOnNhd (by norm_num),?_⟩
  intro z hz
  exact no_domain_extension_of_eqOn highNormalizedBulk_one_eqOn.symm
    (isotropic_high_naturalBoundary.2 z hz)

end
end IsingBulk.Anisotropic
