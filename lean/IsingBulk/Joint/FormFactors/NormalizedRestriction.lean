import IsingBulk.Joint.FormFactors.Restriction
import IsingBulk.Joint.Slices.ExactDomains
import IsingBulk.Anisotropic.Final.PhysicalIdentification

namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set

theorem ratioSlice_analyticAt (lam : ℝ) (z : ℂ) : AnalyticAt ℂ (ratioSlice lam) z :=
  analyticAt_id.prod (analyticAt_const.mul analyticAt_id)

theorem highPrefactor_ratioSlice {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ Anisotropic.omegaH lam) :
    highPrefactor (ratioSlice lam z) = Anisotropic.FormFactors.highPrefactor lam z := by
  have hmem (v : ℂ) (hv : v ∈ Anisotropic.omegaH lam) : ratioSlice lam v ∈ highDomain := by
    change v ∈ ratioSlice lam ⁻¹' highDomain
    rwa [highDomain_pullback hlam]
  have hb : Anisotropic.FormFactors.HighBranch lam (fun v => highPrefactor (ratioSlice lam v)) := by
    refine ⟨fun v hv => (highPrefactor_analyticOnNhd _ (hmem v hv)).comp
      (f := ratioSlice lam) (ratioSlice_analyticAt lam v), ?_, ?_⟩
    · intro v hv
      exact highPrefactor_pow_four (hmem v hv)
    · simp [ratioSlice]
  exact Anisotropic.highBranch_unique hlam hb (Anisotropic.highPrefactor_actual_spec hlam) hz

theorem lowPrefactor_ratioSlice {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ Anisotropic.omegaL lam) :
    lowPrefactor (ratioSlice lam z) = Anisotropic.FormFactors.lowPrefactor lam z := by
  have hmem (v : ℂ) (hv : v ∈ Anisotropic.omegaL lam) : ratioSlice lam v ∈ lowDomain := by
    change v ∈ ratioSlice lam ⁻¹' lowDomain
    rwa [lowDomain_pullback hlam]
  have hb : Anisotropic.FormFactors.LowBranch lam (fun v => lowPrefactor (ratioSlice lam v)) := by
    refine ⟨fun v hv => (lowPrefactor_analyticOnNhd _ (hmem v hv)).comp
      (f := ratioSlice lam) (ratioSlice_analyticAt lam v), ?_, ?_⟩
    · intro v hv
      exact lowPrefactor_pow_four (hmem v hv)
    · intro x hx hp
      change (fourthRoot (1-(Anisotropic.spectralProduct lam (x:ℂ))⁻¹^2)).im = 0 ∧
        0 < (fourthRoot (1-(Anisotropic.spectralProduct lam (x:ℂ))⁻¹^2)).re
      rw [Anisotropic.lowRadicand_real]
      exact fourthRoot_real_positive (Anisotropic.lowRealRadicand_pos hlam
        ((Anisotropic.criticalPoint_lt_iff_product_gt_one hlam hx.le).mpr hp))
  exact Anisotropic.lowBranch_unique hlam hb (Anisotropic.lowPrefactor_actual_spec hlam) hz

theorem highNormalizedBulk_ratioSlice {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ Anisotropic.omegaH lam) :
    highNormalizedBulk (ratioSlice lam z) = Anisotropic.FormFactors.highNormalizedBulk lam z := by
  unfold highNormalizedBulk Anisotropic.FormFactors.highNormalizedBulk
  rw [highPrefactor_ratioSlice hlam hz,p_ratioSlice]
  congr 1


theorem lowNormalizedBulk_ratioSlice {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ Anisotropic.omegaL lam) :
    lowNormalizedBulk (ratioSlice lam z) = Anisotropic.FormFactors.lowNormalizedBulk lam z := by
  unfold lowNormalizedBulk Anisotropic.FormFactors.lowNormalizedBulk
  rw [lowPrefactor_ratioSlice hlam hz,p_ratioSlice]
  congr 1

end
end IsingBulk.Joint.FormFactors
