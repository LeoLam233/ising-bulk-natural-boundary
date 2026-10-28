import IsingBulk.HT22.Tail.LocalizedLift
import IsingBulk.HT22.Tail.ZerothIdentity
import IsingBulk.HT22.Tail.SignedRadialIntegral
import IsingBulk.HT22.Physical.WeightedAnalytic

namespace IsingBulk.HT22.Tail
noncomputable section
open Set Filter MeasureTheory IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

def localizedObservable (negative : Bool) (n : ℕ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (rcut : ℝ → ℝ)
    (W : (Fin (n+1) → ℝ) → ℂ) (t : ℂ) : ℂ :=
  ∫ θ in angularBox n,
    let w := preferredLiftedAngles B.delta (Physical.constrainedAngles negative n θ)
    W w*(preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w:ℂ)*
      Physical.bareContourDensity negative τ B.p B.m t (Physical.constrainedAngles negative n θ)

theorem localized_lifted_weight_continuous {N : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (W : (Fin N → ℝ) → ℂ) (hW : ContDiff ℝ ∞ W)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) :
    Continuous (fun θ : Fin N → ℝ => W (preferredLiftedAngles B.delta θ)*
      (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut (preferredLiftedAngles B.delta θ):ℂ)) := by
  let F := fun z : ℂ × (Fin N → ℝ) => W z.2*
    (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut z.2:ℂ)
  have hF : ContDiff ℝ ∞ F := (hW.comp contDiff_snd).mul
    (Complex.ofRealCLM.contDiff.comp
      ((preferredCellWeight_contDiff .right preferredPopulationCutoff B.p B.m rcut
        preferredPopulationCutoff_smooth B.smooth B.m_smooth hr).comp contDiff_snd))
  have hzero : ∀ s θ i,1/2<B.p (θ i) → F (s,θ)=0 := by
    intro s θ i hi
    have hP : 1/2≤occupancy B.p θ := hi.le.trans
      (Finset.single_le_sum (s := (Finset.univ : Finset (Fin N)))
        (fun v _ => B.lower_bound (θ v)) (Finset.mem_univ i))
    simp only [F,preferredCellWeight,preferredLowerWeight,lowerWeight,
      preferredPopulationCutoff_one hP,sub_self,zero_mul,zero_div,Complex.ofReal_zero,mul_zero]
  apply continuous_iff_continuousAt.mpr
  intro θ
  have hh := preferredLiftedFunction_contDiffAt d B F hzero 0 θ (fun _ => hF.contDiffAt)
  exact (hh.comp θ (contDiffAt_const.prodMk contDiffAt_id)).continuousAt

theorem localizedObservable_analyticAt (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (W : (Fin (n+1) → ℝ) → ℂ) (hW : ContDiff ℝ ∞ W)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) {s : ℂ} (hS : 0<(temperatureTrace s).im) :
    AnalyticAt ℂ (localizedObservable negative n d B τ rcut W) s :=
  Physical.signed_weighted_contour_integral_analyticAt negative n d B hτ _
    (localized_lifted_weight_continuous d B W hW rcut hr) hS

theorem localizedObservable_eq_zero_integral (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (W : (Fin (2*n+1) → ℝ) → ℂ) (rcut : ℝ → ℝ)
    {s : ℂ} (hS : 0<(temperatureTrace s).im) :
    localizedObservable negative (2*n) d B τ rcut W s=
      signedLiftedIntegral (Physical.constraintAngle negative) B.delta
        (localizedPhysicalDensity (Physical.constraintSign negative) τ preferredPopulationCutoff B.p B.m rcut W 0) s := by
  unfold localizedObservable signedLiftedIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    let w := preferredLiftedAngles B.delta (Physical.constrainedAngles negative (2*n) θ)
    have hU (i : Fin (2*n+1)) : 0<(temperatureTrace s-Complex.cos (deformedAngles τ B.p B.m w i)).im := by
      have hh := homotopy_complexW_im_pos hS hτ (by norm_num : (0:ℝ)≤1) B.p B.m w
        B.lower_bound (fun x => B.lower_bound (-x))
        (fun x hx => B.p_zero_of_sin_nonpos hx) (fun x hx => B.m_zero_of_sin_nonneg hx) i
      simpa only [complexW_homotopyRoot_eq] using hh
    have hb := Anchor.weighted_bareContourDensity_eq_seed negative n τ B.p B.m
      (preferredCellWeight .right preferredPopulationCutoff B.p B.m rcut w) s w hU
    have hl := Physical.bareContourDensity_lift negative τ B.delta B.p B.m B.periodic B.m_periodic s
      (Physical.constrainedAngles negative (2*n) θ)
    change W w*_*_=W w*physicalSeed _ _ _ _ _ _ s w
    rw [mul_assoc,←hl]
    exact congrArg (fun q => W w*q) hb

end
end IsingBulk.HT22.Tail
