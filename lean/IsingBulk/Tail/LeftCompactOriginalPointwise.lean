import IsingBulk.Tail.LeftCompactSourceJets
import IsingBulk.Tail.SectorCutoffJetBounds
import IsingBulk.Tail.MixedSectorWeights

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Actual original all-compact left-sector parameter jets. The single
remaining Y kernel is retained for angular integration. -/
theorem left_compact_original_pointwise (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ κ : ℝ,0<α₀ ∧ 0<κ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ C : ℝ,0<C ∧ ∀ᶠ eps : ℝ in 𝓝[>] 0,
      ∀ (N k : ℕ) (τ : ℝ) (θ : Fin N → ℝ) (a q : Fin N) (sigma : Fin N → Fin 3),
      1≤N → k≤order → 0≤τ → θ∈angleBox N → sigma a=0 → (∀ i,sigma i≠2) →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let s := radialParameter d.theta eps
      ‖originalMixedWeight f d.thetaB outer inner ho hi q sigma θ*
        iteratedDeriv k (fun z => pulledDensity f r τ 0 z θ) s‖≤
        C^N*(N:ℝ)^(4*order)*Real.exp (-κ*(N:ℝ)^2)*
          ‖(1-coordinateProduct (deformedPoint f r τ 0 θ))⁻¹‖ := by
  obtain ⟨ηA,hηA,hAmplitude⟩ := mixed_original_regular_amplitude_jets d hcsmall
  refine ⟨min ηA (Real.sin d.thetaB/4),lt_min hηA (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨α₀,κ,hα₀,hκ,hAmplitude⟩ := hAmplitude η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨α₀,κ,hα₀,hκ,?_⟩
  intro α hα hαlt order outer cap ho hcap
  let f := constructedSelector d.thetaB η α
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  obtain ⟨inner₀,hi₀,hicap,hAmplitude⟩ := hAmplitude α hα hαlt order cap hcap
  refine ⟨inner₀,hi₀,hicap,?_⟩
  intro inner hi hinner
  obtain ⟨cA,eA,C,hcA,heA,hC,hAmplitude⟩ := hAmplitude inner hi hinner
  obtain ⟨cR,eR,tR,hcR,heR,htR,hRecip⟩ := left_actual_frozen_Z_reciprocal_jets d hcsmall inner hi
  obtain ⟨B,hB,hRecip⟩ := hRecip order
  obtain ⟨L,hL,hCut⟩ := nested_sector_cutoff_jet_bounds f hf d.thetaB outer inner ho hi 0
  let D := L*1*C*max 1 (2^order*B)
  have hD : 0<D := by dsimp [D]; positivity [zero_lt_one.trans_le hL]
  refine ⟨D,hD,?_⟩
  filter_upwards [self_mem_nhdsWithin,radial_source_eventually_damping d hcsmall,
    (show ∀ᶠ eps : ℝ in 𝓝[>] 0,eps<min eA eR from
      mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds (lt_min heA heR)))] with eps heps hdom hsmall
  intro N k τ θ a q sigma hN hk hτ hθ hσa hσ
  change 0<eps at heps
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  have hW := deformed_sourceW_upper_on_damping (by omega : 0<N) f hf hdom.1 hdom.2.1 hτ le_rfl hdom.2.2 θ
  have hJ := mixedBranchIndexSet_empty sigma hσ
  change ‖originalMixedWeight f d.thetaB outer inner ho hi q sigma θ*
    iteratedDeriv k (fun z => pulledDensity f r τ 0 z θ) s‖≤
    D^N*(N:ℝ)^(4*order)*Real.exp (-κ*(N:ℝ)^2)*‖(1-coordinateProduct (deformedPoint f r τ 0 θ))⁻¹‖
  by_cases hz : angularSelector f θ*nestedSectorWeight d.thetaB outer inner ho hi q sigma θ=0
  · simp only [originalMixedWeight,hz,Complex.ofReal_zero,zero_mul,norm_zero]
    positivity
  have hSource : θ∈tsupport (angularSelector f) := tsupport_mul_subset_left (subset_closure hz)
  have hAssign : θ∈tsupport (sectorAssignmentWeight d.thetaB inner hi sigma) :=
    tsupport_mul_subset_right (tsupport_mul_subset_right (subset_closure hz))
  have hA := hAmplitude N eps θ q sigma [] s hN heps (hsmall.trans_le (min_le_left _ _))
    hθ hSource hAssign (by dsimp [s]; simp; positivity)
  rw [hJ] at hA
  have hR := hRecip η α hη hηsmall hα N eps τ 0 θ a q sigma [] s hN heps
    (hsmall.trans_le (min_le_right _ _)) hτ le_rfl zero_le_one (by simpa using htR)
    hθ hσa (hσ q) hAssign (by dsimp [s]; simp; positivity)
  simp only [hJ] at hR
  have hRj := left_compact_reciprocal_jet_attach hN q s (deformedPoint f r τ 0 θ) hdom.2.2.1
    (fun i => deformedPoint_nonzero f (Real.exp_pos _).ne' τ 0 θ i) hW order hB.le hR
  have hNorm : ‖mixedDensityNormalization f τ 0 θ‖≤(1:ℝ)^N := by
    apply mixedDensityNormalization_norm_le _ _ _ _ zero_le_one
    simp [angularJacobian_zero,Matrix.det_diagonal,norm_pow]
  have hw : ‖originalMixedWeight f d.thetaB outer inner ho hi q sigma θ‖≤L^N := by
    simpa only [originalMixedWeight,Complex.norm_real,cutoffJet] using (hCut N q sigma [] (by simp) θ).2.1
  exact compact_weighted_density_gaussian_bound hN q f (Real.exp_pos _) τ 0 s θ hdom.2.2.1 hW order k hk
    _ hC.le hB.le zero_le_one (zero_le_one.trans hL)
    (by simpa only [deformedPoint_zero] using hA) hRj hNorm hw

end
end IsingBulk.Tail
