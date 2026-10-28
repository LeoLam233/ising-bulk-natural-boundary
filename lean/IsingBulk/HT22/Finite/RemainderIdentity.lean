import IsingBulk.HT22.Physical.FiniteAssembly.LocalizedRight
import IsingBulk.HT22.Anchor.PhysicalSeed
import IsingBulk.HT22.Geometry.SeparatedRemainder
import IsingBulk.HT22.Tail.LocalizedSeed
namespace IsingBulk.HT22.Finite
noncomputable section
open Set Filter MeasureTheory IsingBulk.Preferred22 IsingBulk.HT22.Physical
open IsingBulk.HT22.Physical.FiniteAssembly IsingBulk.HT22.Geometry
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem separated_remainder_integral_identity (negative : Bool) (k : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δ R τ : ℝ}
    (hR : 0<R) (hτ : 0≤τ) (r : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δ r)
    (rem : (Fin (2*k) → ℝ) → ℝ)
    (hfar : ∀ θ∈signedRightRegion (constraintAngle negative) d B δ,rem θ≠0 →
      R<preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAtTotal (constraintAngle negative) θ)))
    {t : ℂ} (hS : 0<(temperatureTrace t).im) :
    localizedRightIntegral negative (2*k) τ B.p B.m r rem t=
      ∫ θ : Fin (2*k) → ℝ in angularBox (2*k),
        Tail.localizedPhysicalDensity (constraintSign negative) τ preferredPopulationCutoff B.p B.m r
          (separatedAmbientRemainder R rem) 0 t
          (preferredLiftedAngles B.delta (constrainedAtTotal (constraintAngle negative) θ)) := by
  rw [localizedRightIntegral_eq_lifted negative (2*k) d B τ r hcut.2.2.2.1]
  unfold localizedSignedLiftedIntegral
  apply setIntegral_congr_fun (MeasurableSet.univ_pi (fun _ => measurableSet_Ioc))
  intro θ hθ
  let w := preferredLiftedAngles B.delta (constrainedAtTotal (constraintAngle negative) θ)
  have hW (i : Fin (2*k+1)) : 0<(temperatureTrace t-Complex.cos (deformedAngles τ B.p B.m w i)).im := by
    have hh := homotopy_complexW_im_pos hS hτ (by norm_num : (0:ℝ)≤1) B.p B.m w
      B.lower_bound (fun x => B.lower_bound (-x))
      (fun _ hx => B.p_zero_of_sin_nonpos hx) (fun _ hx => B.m_zero_of_sin_nonneg hx) i
    simpa only [complexW_homotopyRoot_eq] using hh
  have hseed := Anchor.weighted_bareContourDensity_eq_seed negative k τ B.p B.m
    (preferredCellWeight .right preferredPopulationCutoff B.p B.m r w) t w hW
  have heq := separatedAmbientRemainder_weighted_lift_eq d B hR r hcut (constraintAngle negative) rem hfar θ hθ
  change separatedAmbientRemainder R rem w*(preferredCellWeight .right preferredPopulationCutoff B.p B.m r w:ℂ)=_ at heq
  change (rem θ:ℂ)*Geometry.rightContourWeight τ preferredPopulationCutoff B.p B.m r w*
    complexSignedDensity negative (t,deformedAngles τ B.p B.m w)=
    separatedAmbientRemainder R rem w*Anchor.physicalSeed (constraintSign negative) τ B.p B.m
      (preferredCellWeight .right preferredPopulationCutoff B.p B.m r w) t w
  rw [←hseed,mul_assoc,Geometry.rightContourWeight_density,←mul_assoc,←mul_assoc,heq]

theorem separated_remainder_derivative_identity (negative : Bool) (k : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δ R τ : ℝ}
    (hR : 0<R) (hτ : 0≤τ) (r : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δ r)
    (rem : (Fin (2*k) → ℝ) → ℝ)
    (hfar : ∀ θ∈signedRightRegion (constraintAngle negative) d B δ,rem θ≠0 →
      R<preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAtTotal (constraintAngle negative) θ)))
    {s : ℂ} (hS : 0<(temperatureTrace s).im) (j : ℕ) :
    iteratedDeriv j (localizedRightIntegral negative (2*k) τ B.p B.m r rem) s=
      iteratedDeriv j (fun t => ∫ θ : Fin (2*k) → ℝ in angularBox (2*k),
        Tail.localizedPhysicalDensity (constraintSign negative) τ preferredPopulationCutoff B.p B.m r
          (separatedAmbientRemainder R rem) 0 t
          (preferredLiftedAngles B.delta (constrainedAtTotal (constraintAngle negative) θ))) s := by
  apply Filter.EventuallyEq.iteratedDeriv_eq
  obtain ⟨ρ,hρ,hU⟩ := preferred_trace_upper_neighborhood hS
  filter_upwards [Metric.ball_mem_nhds s hρ] with t ht
  exact separated_remainder_integral_identity negative k d B hR hτ r hcut rem hfar (hU t ht).2
end
end IsingBulk.HT22.Finite
