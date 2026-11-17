import IsingBulk.Anisotropic.Final.CompleteTarget
import IsingBulk.AnisoF002.C03.PhysicalCovarianceAttachment

/-!
# Literal uniform energy-field response from the constructed real-lattice sum

Only the separately inspected generic finite-spin/GHS squeeze and generic
odd-function derivative lemma are reused.  Original field-response or
natural-boundary endpoints are not invoked.  The exact full-lattice
summability is supplied by the independently constructed physical
identification, and beta remains x/(2J).
-/

namespace IsingBulk.AnisoF002.Physical
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.Anisotropic.PhysicalField Set

theorem original_gibbs_high_derivative_of_summable {J lam : ℝ} (hJ : 0 < J)
    {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ}
    (hG : PublishedRealGibbsFields J lam corrH corrL mH mL)
    {x : ℝ} (hx : 0 < x) (hp : realProduct lam x < 1) (hc : Summable (corrH x)) :
    HasDerivAt (mH x) (highEnergyFieldResponse J corrH x) 0 := by
  apply hasDerivAt_of_odd_right_derivative (hG.high_spin_flip x hx hp)
  exact field_response_of_gibbs_conditions
    (div_pos hx (mul_pos (by norm_num) hJ)).le (Classical.choice (hG.high x hx hp)) hc

theorem original_gibbs_low_right_derivative_of_summable {J lam : ℝ} (hJ : 0 < J)
    {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ}
    (hG : PublishedRealGibbsFields J lam corrH corrL mH mL)
    {x : ℝ} (hx : 0 < x) (hp : 1 < realProduct lam x)
    (hc : Summable (fun v => corrL x v - realMagnetizationSq lam x)) :
    HasDerivWithinAt (mL x) (lowEnergyFieldResponse J lam corrL x) (Ioi 0) 0 := by
  exact field_response_of_gibbs_conditions
    (div_pos hx (mul_pos (by norm_num) hJ)).le (Classical.choice (hG.low x hx hp)) hc

/-- All five original field-identification fields, with bilateral HT and
plus-phase right LT derivatives and the original connected subtraction. -/
theorem literal_uniformField_of_realIdentification {J lam : ℝ} (hJ : 0 < J)
    {corrH corrL : ℝ → LatticeSite → ℝ} {mH mL : ℝ → ℝ → ℝ}
    (hG : PublishedRealGibbsFields J lam corrH corrL mH mL)
    (hID : RealPhysicalIdentification J lam corrH corrL) :
    RealUniformFieldIdentification J lam corrH corrL mH mL := by
  refine ⟨?_, ?_, ?_, hG.low_zero_square, hG.low_plus_positive⟩
  · intro x hx hp
    exact original_gibbs_high_derivative_of_summable hJ hG hx hp (hID.high x hx hp).1
  · intro x hx hp
    have hh := hG.high_spin_flip x hx hp 0
    simp only [neg_zero] at hh
    linarith
  · intro x hx hp
    exact original_gibbs_low_right_derivative_of_summable hJ hG hx hp (hID.low x hx hp).1

end
end IsingBulk.AnisoF002.Physical
