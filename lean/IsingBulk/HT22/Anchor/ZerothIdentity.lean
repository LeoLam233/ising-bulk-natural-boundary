import IsingBulk.HT22.Anchor.LiftedRegularity
import IsingBulk.HT22.Physical.LiftIdentity
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set MeasureTheory IsingBulk.Preferred22
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem transportedIntegral_zero (negative : Bool) (n : ℕ) (a : Fin (2*n+1))
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (τ : ℝ) (hτ : 0≤τ)
    (r : ℝ → ℝ) (hr : Function.Periodic r (2*Real.pi)) (s : ℂ)
    (hSi : 0<(temperatureTrace s).im) :
    transportedIntegral negative (2*n) a B.delta τ preferredPopulationCutoff B.p B.m r 0 s=
      Physical.anchorPopulationIntegral negative (2*n) a τ preferredPopulationCutoff B.p B.m r s := by
  have hmp : Function.Periodic B.m (2*Real.pi) := by
    intro x
    change B.p (-(x+2*Real.pi))=B.p (-x)
    convert (B.periodic (-x-2*Real.pi)).symm using 1 <;> congr 1 <;> ring
  unfold transportedIntegral Physical.anchorPopulationIntegral Physical.weightedContourIntegral
  apply setIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))
  intro θ _
  let w := preferredLiftedAngles B.delta (Physical.constrainedAngles negative (2*n) θ)
  have hW (i : Fin (2*n+1)) : 0<(temperatureTrace s-Complex.cos (deformedAngles τ B.p B.m w i)).im := by
    have hh := homotopy_complexW_im_pos hSi hτ (by norm_num : (0:ℝ)≤1) B.p B.m w
      B.lower_bound (fun x => B.lower_bound (-x))
      (fun x hx => B.p_zero_of_sin_nonpos hx) (fun x hx => B.m_zero_of_sin_nonneg hx) i
    simpa only [complexW_homotopyRoot_eq] using hh
  change physicalSeed (Physical.constraintSign negative) τ B.p B.m
    (preferredCellWeight (.anchor a) preferredPopulationCutoff B.p B.m r w) s w=_
  rw [←weighted_bareContourDensity_eq_seed negative n τ B.p B.m _ s w hW]
  dsimp only [w]
  rw [preferredCellWeight_lift (.anchor a) B.delta preferredPopulationCutoff B.p B.m r B.periodic hmp hr,
    Physical.bareContourDensity_lift negative τ B.delta B.p B.m B.periodic hmp]
end
end IsingBulk.HT22.Anchor
