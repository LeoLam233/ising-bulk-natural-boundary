import IsingBulk.Anisotropic.Final.ActualHolomorphy
import IsingBulk.Anisotropic.Geometry.DomainSymmetries
import IsingBulk.Anisotropic.FormFactors.AxisExchange

namespace IsingBulk.Anisotropic
noncomputable section
open Set FormFactors

theorem highPrefactor_axis_exchange {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hz : z∈omegaH lam) :
    highPrefactor (lam⁻¹) ((lam:ℂ)*z)=highPrefactor lam z := by
  have hs := highPrefactor_actual_spec (inv_pos.mpr hlam)
  have hf : HighBranch lam (fun w => highPrefactor (lam⁻¹) ((lam:ℂ)*w)) := by
    refine ⟨fun w hw => (hs.1 _ (omegaH_axis_exchange hlam hw)).comp
      (analyticAt_const.mul analyticAt_id),?_,?_⟩
    · intro w hw
      simpa only [spectralProduct_axis_exchange hlam.ne'] using hs.2.1 _ (omegaH_axis_exchange hlam hw)
    · simpa only [mul_zero] using hs.2.2
  exact highBranch_unique hlam hf (highPrefactor_actual_spec hlam) hz

theorem lowPrefactor_axis_exchange {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hz : z∈omegaL lam) :
    lowPrefactor (lam⁻¹) ((lam:ℂ)*z)=lowPrefactor lam z := by
  have hs := lowPrefactor_actual_spec (inv_pos.mpr hlam)
  have hf : LowBranch lam (fun w => lowPrefactor (lam⁻¹) ((lam:ℂ)*w)) := by
    refine ⟨fun w hw => (hs.1 _ (omegaL_axis_exchange hlam hw)).comp
      (analyticAt_const.mul analyticAt_id),?_,?_⟩
    · intro w hw
      simpa only [spectralProduct_axis_exchange hlam.ne'] using hs.2.1 _ (omegaL_axis_exchange hlam hw)
    · intro x hx hp
      have ha : lam⁻¹*(lam*x)=x := by field_simp
      have hp' : 1<Real.sinh (lam*x)*Real.sinh (lam⁻¹*(lam*x)) := by
        rw [ha,mul_comm]
        exact hp
      simpa only [Complex.ofReal_mul] using hs.2.2 (lam*x) (mul_pos hlam hx) hp'
  exact lowBranch_unique hlam hf (lowPrefactor_actual_spec hlam) hz

theorem highNormalizedBulk_axis_exchange {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hz : z∈omegaH lam) :
    highNormalizedBulk (lam⁻¹) ((lam:ℂ)*z)=highNormalizedBulk lam z := by
  unfold highNormalizedBulk
  rw [highPrefactor_axis_exchange hlam hz,spectralProduct_axis_exchange hlam.ne']
  congr 1
  apply tsum_congr
  intro n
  rw [unscaledFullCoefficient_axis_exchange (2*n+1) (by omega) hlam.ne'
    (omegaH_subset_spectral_complement hlam hz)]

theorem lowNormalizedBulk_axis_exchange {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hz : z∈omegaL lam) :
    lowNormalizedBulk (lam⁻¹) ((lam:ℂ)*z)=lowNormalizedBulk lam z := by
  unfold lowNormalizedBulk
  rw [lowPrefactor_axis_exchange hlam hz,spectralProduct_axis_exchange hlam.ne']
  congr 1
  apply tsum_congr
  intro n
  rw [unscaledFullCoefficient_axis_exchange (2*n+2) (by omega) hlam.ne'
    (omegaL_subset_spectral_complement hlam hz)]

end
end IsingBulk.Anisotropic
