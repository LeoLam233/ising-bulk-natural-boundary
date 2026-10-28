import IsingBulk.HT22.Tail.PuncturedGeometry
import IsingBulk.HT22.Tail.SignedStokes
import IsingBulk.Preferred22.PunctureFlux

/-! Original transported density is measurable on the signed torus by a
proved smooth puncture exhaustion, with only the actual collision null set
removed. No measurability premise is hidden in the shell norm bounds. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Geometry Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem transportedDensity_aestronglyMeasurable {n : ℕ} (hn : 0<n)
    (a : ℝ) (σ : ℂ) (hσ : ‖σ‖≤1) (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB τ : ℝ} (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (s : ℂ) (j : ℕ)
    (hreg : ∀ x∈preferredRightAngularBox d B.delta δB (n+1),0<preferredAngularDiameter x →
      RegularPoint τ B.p B.m s x) :
    AEStronglyMeasurable (fun θ : Fin n → ℝ =>
      transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j s
        (preferredLiftedAngles B.delta (constrainedAtTotal a θ))) (volume.restrict (angularBox n)) := by
  let P := fun θ : Fin n → ℝ => transportedDensity σ τ preferredPopulationCutoff B.p B.m rcut j s
    (preferredLiftedAngles B.delta (constrainedAtTotal a θ))
  let F := fun m (θ : Fin n → ℝ) => puncturedDensity σ d B τ (preferredDyadicRadius m) rcut j s
    (preferredLiftedAngles B.delta (constrainedAtTotal a θ))
  have hF (m : ℕ) : AEStronglyMeasurable (F m) (volume.restrict (angularBox n)) := by
    have hc : ContDiff ℝ ∞ (F m) := by
      apply contDiff_iff_contDiffAt.mpr
      intro θ
      have hh := (puncturedDensity_and_current_lift_contDiffAt (by omega) σ hσ d B rcut hcut
        s (preferredDyadicRadius m) j hreg (constrainedAtTotal a θ)).1
      exact hh.comp θ (contDiffAt_const.prodMk (constrainedAtTotal_contDiff a).contDiffAt)
    exact hc.continuous.aestronglyMeasurable
  have hbox : MeasurableSet (angularBox n) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)
  have hnull := signedRightCollision_null hn a d B hcut.2.1
  have hncoll : ∀ᵐ θ : Fin n → ℝ ∂volume, θ∉signedRightCollision a d B δB := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hnull
  apply aestronglyMeasurable_of_tendsto_ae atTop hF
  filter_upwards [ae_restrict_of_ae hncoll,ae_restrict_mem hbox] with θ hnc hθ
  change Tendsto (fun m => F m θ) atTop (𝓝 (P θ))
  by_cases hb : θ∈signedRightRegion a d B δB
  · let w := preferredLiftedAngles B.delta (constrainedAtTotal a θ)
    have hd : 0<preferredAngularDiameter w := by
      by_contra hh
      have hz : preferredAngularDiameter w=0 := le_antisymm (le_of_not_gt hh) Metric.diam_nonneg
      apply hnc
      refine ⟨hb,?_⟩
      intro i k
      have hp := preferredAngularDiameter_pair_le w i k
      rw [hz] at hp
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hp (abs_nonneg _)))
    have he : (fun m => F m θ)=ᶠ[atTop] (fun _ => P θ) := by
      filter_upwards [preferredEqualityCutoff_eventually_one w hd] with m hm
      change (preferredEqualityCutoff (preferredDyadicRadius m) w:ℂ)*P θ=P θ
      rw [hm,Complex.ofReal_one,one_mul]
    exact tendsto_const_nhds.congr' he.symm
  · have hz : P θ=0 := transportedDensity_right_support σ d B τ rcut hcut j s _
      (preferredLiftedAngles_mem_oneSided B.delta (constrainedAtTotal a θ))
      (by intro hh; exact hb ⟨hθ,hh⟩)
    have he : (fun m => F m θ)=fun _ => (0:ℂ) := by
      funext m
      change (preferredEqualityCutoff (preferredDyadicRadius m) _:ℂ)*P θ=0
      rw [hz,mul_zero]
    rw [he,hz]
    exact tendsto_const_nhds

end
end IsingBulk.HT22.Tail
