import IsingBulk.Preferred22.AnchorProfileMass
import IsingBulk.Preferred22.AnchorRadialIntegral

/-! Genuine integration of the anchored independent envelope. The complete
constrained angular integral and its original normalization are retained. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Every actual anchored descendant is genuinely integrable on the
complete angular box, by its proved smooth one-sided lift. -/
theorem preferred_anchor_density_integrable {n : ℕ}
    (d : PreferredBranchData) (B : PreferredCoareaBump d) (a : Fin (n+1)) (τ : ℝ)
    (rcut : ℝ → ℝ) (hr : ContDiff ℝ ∞ rcut) (s : ℂ) (j : ℕ)
    (hreg : ∀ x : Fin (n+1) → ℝ,(∀ i,x i∈Icc (-Real.pi-B.delta) B.delta) →
      (s,x)∈preferredCellRegularDomain (.anchor a) τ B.p B.m) :
    IntegrableOn (fun θ : Fin n → ℝ => preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff
      B.p B.m rcut j s (preferredLiftedAngles B.delta (constrainedAngles θ))) (angularBox n) := by
  have hc : Continuous (fun x : Fin (n+1) → ℝ => preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff
      B.p B.m rcut j s (preferredLiftedAngles B.delta x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((preferredAnchor_density_current_lift_contDiffAt (by omega) d B a τ rcut hr s j hreg x).1.continuousAt).comp
      (continuousAt_const.prodMk continuousAt_id)
  exact continuous_integrableOn_angularBox (hc.comp (constrainedAngles_continuous n))

/-- Exact profile integration for every retained even particle order,
including N=2. No density integrability is supplied as an assumption. -/
theorem preferred_anchor_integral_profile_bound (d : PreferredBranchData) :
    ∃ D>0,∀ n : ℕ,2≤n+1 → Even (n+1) → ∀ ε : ℝ,0<ε → ε≤1 →
      ∀ B : PreferredCoareaBump d,∀ τ : ℝ,∀ rcut : ℝ → ℝ,∀ j : ℕ,∀ s : ℂ,∀ a : Fin (n+1),
      ∀ A : ℝ,0≤A →
      (∀ θ : Fin n → ℝ,‖preferredTransportedDensity (.anchor a) τ preferredPopulationCutoff B.p B.m rcut j s
        (preferredLiftedAngles B.delta (constrainedAngles θ))‖≤A*preferredAnchorProfile d ε a (constrainedAngles θ)) →
      ‖preferredTransportedIntegral (.anchor a) B.delta τ preferredPopulationCutoff B.p B.m rcut j s‖≤A*D^(n+1) := by
  obtain ⟨D,hD,hmass⟩ := preferred_anchor_profile_mass d
  refine ⟨D,hD,?_⟩
  intro n hn he ε hε hε1 B τ rcut j s a A hA hbound
  have hi := (preferredAnchorProfile_integrable d n hε a).const_mul A
  have hh := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hbound)
  change ‖preferredTransportedIntegral (.anchor a) B.delta τ preferredPopulationCutoff B.p B.m rcut j s‖≤_ at hh
  rw [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (hmass n hn he ε hε hε1 a) hA)

end
end IsingBulk.Preferred22
