import IsingBulk.HT22.Tail.LocalizedMassSupport

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false

theorem localized_derivative_bound_of_mass (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ δB ε₀ : ℝ} (hτ : 0≤τ)
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (W : (Fin (2*n+1) → ℝ) → ℂ) (hW : ContDiff ℝ ∞ W)
    (hzero : ∀x∈preferredRightAngularBox d B.delta δB (2*n+1), preferredAngularDiameter x=0 → W=ᶠ[𝓝 x] fun _=>0)
    (hreg : ∀ε∈Ioo 0 ε₀,∀x∈preferredRightAngularBox d B.delta δB (2*n+1),
      0<preferredAngularDiameter x → RegularPoint τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) x)
    (j : ℕ) {ε M : ℝ} (hε : 0<ε) (hεr : ε<ε₀) (hM : 0≤M)
    (hmass : (∫⁻θ : Fin (2*n) → ℝ in Geometry.signedRightRegion (Physical.constraintAngle negative) d B δB,
      ENNReal.ofReal ‖localizedPhysicalDensity (Physical.constraintSign negative) τ preferredPopulationCutoff B.p B.m rcut W j
        (IsingBulk.Branch.radialParameter d.alpha ε)
        (preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ))‖)≤ENNReal.ofReal M) :
    ‖iteratedDeriv j (localizedObservable negative (2*n) d B τ rcut W)
      (IsingBulk.Branch.radialParameter d.alpha ε)‖≤M := by
  rw [localized_integral_identity negative n d B hτ rcut hcut W hW hzero hreg j ε hε hεr]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  rw [ENNReal.toReal_ofReal hM] at hh
  unfold signedLiftedIntegral
  apply (norm_integral_le_lintegral_norm _).trans
  rw [localizedNorm_lintegral_eq_signedRightRegion (Physical.constraintSign negative)
    (Physical.constraintAngle negative) d B τ rcut W hcut j]
  exact hh

end
end IsingBulk.HT22.Tail
