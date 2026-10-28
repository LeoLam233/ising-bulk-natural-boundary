import IsingBulk.HT22.Anchor.Support
import IsingBulk.Preferred22.AnchorJacobianProfile
import IsingBulk.Preferred22.AnchorProfileMass
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set IsingBulk.Preferred22
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Complete odd anchor profile bound on the full lifted angular contour.
Only the unchanged coordinate Jacobian profile is reused; the density,
field, recurrence and all scalar bounds are the new HT22 ones. -/
theorem actual_anchor_pointwise_bound (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut →
      ∀ J : ℕ,∃ C : ℝ,0<C ∧
      ∀ N : ℕ,0<N → ∀ σ : ℂ,‖σ‖=1 → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,∀ a : Fin N,∀ j≤J,
      ‖transportedDensity a σ τ preferredPopulationCutoff B.p B.m rcut j
        (IsingBulk.Branch.radialParameter d.alpha ε) (preferredLiftedAngles B.delta θ)‖≤
        ((C/Real.sqrt N)^N*(N:ℝ)^(J*J+8*J+1))*preferredAnchorProfile d ε a θ := by
  obtain ⟨capS,hcapS,hcapSa,hscalar⟩ := actual_anchor_scalar_bound d
  obtain ⟨capQ,hcapQ,_hcapQa,hjac⟩ := preferred_actual_anchor_Jacobian_profile d
  refine ⟨min capS capQ,lt_min hcapS hcapQ,(min_le_left _ _).trans_lt hcapSa,?_⟩
  intro B hB δB hδB
  obtain ⟨εs,τs,hεs,hτs,hscalar'⟩ := hscalar B (hB.trans_le (min_le_left _ _)) δB hδB
  obtain ⟨Q,εq,τq,hQ,hεq,hτq,hjac'⟩ := hjac B (hB.trans_le (min_le_right _ _)) δB hδB
  refine ⟨min εs εq,min τs τq,lt_min hεs hεq,lt_min hτs hτq,?_⟩
  intro rcut hcut J
  obtain ⟨A,hA,hsource⟩ := hscalar' rcut hcut.2.2.1 hcut.2.2.2.1 J
  refine ⟨Q*A,mul_pos hQ (zero_lt_one.trans_le hA),?_⟩
  intro N hN σ hσ ε τ hε hεr hτ hτr θ a j hj
  let w := preferredLiftedAngles B.delta θ
  by_cases hcore : (∀ i,w i∈Icc (-Real.pi-B.delta) B.delta) ∧ w a≤ -d.b-δB/2
  · have hs := hsource N hN σ hσ ε τ hε (hεr.trans_le (min_le_left _ _)) hτ
      (hτr.trans_le (min_le_left _ _)) w hcore.1 a hcore.2 j hj
    have hq := hjac' N hN ε τ hε (hεr.trans_le (min_le_right _ _)) hτ
      (hτr.trans_le (min_le_right _ _)) w hcore.1 a hcore.2
    dsimp only at hs
    rw [Tail.coordinateJacobian_eq_shared] at hs
    apply hs.trans
    calc
      _ ≤ (Q^N*preferredAnchorProfile d ε a w)*((A/Real.sqrt N)^N*(N:ℝ)^(J*J+8*J+1)) :=
        mul_le_mul_of_nonneg_right hq (by have := zero_le_one.trans hA; positivity)
      _ = _ := by
        rw [preferredAnchorProfile_lift]
        simp only [mul_pow,div_pow]
        ring
  · rw [transportedDensity_anchor_support d B σ a τ rcut hcut j _ w
      (preferredLiftedAngles_mem_oneSided B.delta θ) hcore,norm_zero]
    exact mul_nonneg (by have := zero_le_one.trans hA; positivity)
      (preferredAnchorProfile_nonneg d hε a θ)

end
end IsingBulk.HT22.Anchor
