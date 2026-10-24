import IsingBulk.Anisotropic.Final.LowPrefactor
import IsingBulk.Anisotropic.FormFactors.NormalConvergence
import IsingBulk.Anisotropic.Final.Target

namespace IsingBulk.Anisotropic
noncomputable section

theorem highNormalizedBulk_analyticOnNhd {lam : ℝ} (hlam : 0<lam) :
    AnalyticOnNhd ℂ (FormFactors.highNormalizedBulk lam) (omegaH lam) := by
  intro z hz
  exact ((highPrefactor_actual_spec hlam).1 z hz).mul
    (FormFactors.high_particleSeries_analyticOnNhd lam z
      (omegaH_subset_spectral_complement hlam hz))

theorem lowNormalizedBulk_analyticOnNhd {lam : ℝ} (hlam : 0<lam) :
    AnalyticOnNhd ℂ (FormFactors.lowNormalizedBulk lam) (omegaL lam) := by
  intro z hz
  exact ((lowPrefactor_actual_spec hlam).1 z hz).mul
    (FormFactors.low_particleSeries_analyticOnNhd lam z
      (omegaL_subset_spectral_complement hlam hz))

theorem highPhysicalBulk_analyticOnNhd (J : ℝ) {lam : ℝ} (hlam : 0<lam) :
    AnalyticOnNhd ℂ (highPhysicalBulk J lam) (omegaH lam) := by
  intro z hz
  exact (inverseTemperature_analytic J z).mul (highNormalizedBulk_analyticOnNhd hlam z hz)

theorem lowPhysicalBulk_analyticOnNhd (J : ℝ) {lam : ℝ} (hlam : 0<lam) :
    AnalyticOnNhd ℂ (lowPhysicalBulk J lam) (omegaL lam) := by
  intro z hz
  exact (inverseTemperature_analytic J z).mul (lowNormalizedBulk_analyticOnNhd hlam z hz)

end
end IsingBulk.Anisotropic
