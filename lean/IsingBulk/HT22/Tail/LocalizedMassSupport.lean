import IsingBulk.HT22.Tail.LocalizedIntegralIdentity
import IsingBulk.HT22.Geometry.SeparatedRemainder
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Geometry Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff ENNReal

/-- The unchanged full actual nonnegative right mass equals the region
mass, without any assumed integrability or a hidden support condition. -/
theorem localizedNorm_lintegral_eq_signedRightRegion {n : ℕ}
    (σ : ℂ) (a : ℝ) (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ}
    (τ : ℝ) (rcut : ℝ → ℝ) (W : (Fin (n+1) → ℝ) → ℂ) (hcut : PreferredRightCutoffData d B δB rcut)
    (j : ℕ) (s : ℂ) :
    (∫⁻ θ in angularBox n,ENNReal.ofReal ‖localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W j s
      (preferredLiftedAngles B.delta (constrainedAtTotal a θ))‖)=
    ∫⁻ (θ : Fin n → ℝ) in signedRightRegion a d B δB,ENNReal.ofReal ‖localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W j s
      (preferredLiftedAngles B.delta (constrainedAtTotal a θ))‖ := by
  let f := fun θ : Fin n → ℝ => ENNReal.ofReal ‖localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W j s
    (preferredLiftedAngles B.delta (constrainedAtTotal a θ))‖
  have hbox : MeasurableSet (angularBox n) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hsupp : Function.support ((angularBox n).indicator f)⊆signedRightRegion a d B δB := by
    intro θ hθ
    by_contra hn
    by_cases hb : θ∈angularBox n
    · have hz := localizedPhysicalDensity_right_support σ d B τ rcut W hcut j s _
        (preferredLiftedAngles_mem_oneSided B.delta (constrainedAtTotal a θ))
        (by intro hh; exact hn ⟨hb,hh⟩)
      have hf : f θ=0 := by dsimp [f]; rw [hz,norm_zero,ENNReal.ofReal_zero]
      exact hθ (by rw [Set.indicator_of_mem hb,hf])
    · exact hθ (Set.indicator_of_notMem hb _)
  apply le_antisymm
  · calc
      _ = ∫⁻ θ,(angularBox n).indicator f θ := (lintegral_indicator hbox f).symm
      _ = ∫⁻ (θ : Fin n → ℝ) in signedRightRegion a d B δB,(angularBox n).indicator f θ :=
        (setLIntegral_eq_of_support_subset hsupp).symm
      _ ≤ _ := lintegral_mono (Set.indicator_le_self _ _)
  · exact lintegral_mono_set (fun θ hθ => hθ.1)


theorem separated_density_zero_small {n : ℕ} (σ : ℂ) (τ : ℝ) (η p m rcut : ℝ → ℝ)
    {R : ℝ} (hR : 0<R) (rem : (Fin n → ℝ) → ℝ) (j : ℕ) (s : ℂ) (θ : Fin (n+1) → ℝ)
    (hθ : preferredAngularDiameter θ<R/(2*((n+1:ℕ):ℝ))) :
    localizedPhysicalDensity σ τ η p m rcut (separatedAmbientRemainder R rem) j s θ=0 :=
  (localizedPhysicalDensity_zero_germ σ τ η p m rcut (separatedAmbientRemainder R rem) θ
    (separatedAmbientRemainder_zero_germ_small hR rem θ hθ) j s).self_of_nhds

end
end IsingBulk.HT22.Tail
