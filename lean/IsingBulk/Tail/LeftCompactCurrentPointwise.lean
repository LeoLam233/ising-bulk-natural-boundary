import IsingBulk.Tail.LeftCompactOriginalPointwise
import IsingBulk.Tail.SelectorJacobianBounds

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- All-compact left-current jets retain both the full angular determinant
and the actual current multiplier; lambda is uniform on its small region. -/
theorem left_compact_current_pointwise (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ τ₀ : ℝ,0<α₀ ∧ 0<τ₀ ∧ ∀ α τ : ℝ,0<α → α<α₀ → 0<τ → τ<τ₀ →
      ∃ κ : ℝ,0<κ ∧ ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ t C : ℝ,0<t ∧ 0<C ∧ ∀ᶠ eps : ℝ in 𝓝[>] 0,
      ∀ (N k : ℕ) (lam : ℝ) (θ : Fin N → ℝ) (a q qA : Fin N) (sigma : Fin N → Fin 3),
      1≤N → k≤order → 0≤lam → lam≤1 → lam*τ<t → θ∈angleBox N → sigma a=0 → (∀ i,sigma i≠2) →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let s := radialParameter d.theta eps
      ‖currentMixedWeight f d.thetaB outer inner ho hi q qA sigma τ θ*
        iteratedDeriv k (fun z => pulledDensity f r τ lam z θ) s‖≤
        C^N*(N:ℝ)^(4*order)*Real.exp (-κ*(N:ℝ)^2)*
          ‖(1-coordinateProduct (deformedPoint f r τ lam θ))⁻¹‖ := by
  obtain ⟨ηA,hηA,hAmplitude⟩ := mixed_current_regular_amplitude_jets d hcsmall
  refine ⟨min ηA (Real.sin d.thetaB/4),lt_min hηA (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨α₀,τ₀,hα₀,hτ₀,hAmplitude⟩ := hAmplitude η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨α₀,τ₀,hα₀,hτ₀,?_⟩
  intro α τ hα hαlt hτ hτlt
  let f := constructedSelector d.thetaB η α
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  obtain ⟨H,hH,hJac⟩ := constructed_selector_jacobian_bound d.thetaB η α τ d.a_pos hη hηsmall hα hτ.le
  obtain ⟨κ,hκ,hAmplitude⟩ := hAmplitude α τ hα hαlt hτ hτlt
  refine ⟨κ,hκ,?_⟩
  intro order outer cap ho hcap
  obtain ⟨inner₀,hi₀,hicap,hAmplitude⟩ := hAmplitude order cap hcap
  refine ⟨inner₀,hi₀,hicap,?_⟩
  intro inner hi hinner
  obtain ⟨cA,eA,tA,C,hcA,heA,htA,hC,hAmplitude⟩ := hAmplitude inner hi hinner
  obtain ⟨cR,eR,tR,hcR,heR,htR,hRecip⟩ := left_actual_frozen_Z_reciprocal_jets d hcsmall inner hi
  obtain ⟨B,hB,hRecip⟩ := hRecip order
  obtain ⟨L,hL,hCut⟩ := nested_sector_cutoff_jet_bounds f hf d.thetaB outer inner ho hi 0
  let M := max 1 (2*τ)
  have hM : 0<M := zero_lt_one.trans_le (le_max_left _ _)
  let D := (M*L)*H*C*max 1 (2^order*B)
  have hD : 0<D := by dsimp [D]; positivity [zero_lt_one.trans_le hL]
  refine ⟨min tA tR,D,lt_min htA htR,hD,?_⟩
  filter_upwards [self_mem_nhdsWithin,radial_source_eventually_damping d hcsmall,
    (show ∀ᶠ eps : ℝ in 𝓝[>] 0,eps<min eA eR from
      mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds (lt_min heA heR)))] with eps heps hdom hsmall
  intro N k lam θ a q qA sigma hN hk hl0 hl1 htl hθ hσa hσ
  change 0<eps at heps
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  have hW := deformed_sourceW_upper_on_damping (by omega : 0<N) f hf hdom.1 hdom.2.1 hτ.le hl0 hdom.2.2 θ
  have hJ := mixedBranchIndexSet_empty sigma hσ
  change ‖currentMixedWeight f d.thetaB outer inner ho hi q qA sigma τ θ*
    iteratedDeriv k (fun z => pulledDensity f r τ lam z θ) s‖≤
    D^N*(N:ℝ)^(4*order)*Real.exp (-κ*(N:ℝ)^2)*‖(1-coordinateProduct (deformedPoint f r τ lam θ))⁻¹‖
  by_cases hz : namedSelectorDerivative f q θ*nestedSectorWeight d.thetaB outer inner ho hi qA sigma θ=0
  · simp only [currentMixedWeight,hz,Complex.ofReal_zero,mul_zero,zero_mul,norm_zero]
    positivity
  have hSource : θ∈tsupport (namedSelectorDerivative f q) := tsupport_mul_subset_left (subset_closure hz)
  have hAssign : θ∈tsupport (sectorAssignmentWeight d.thetaB inner hi sigma) :=
    tsupport_mul_subset_right (tsupport_mul_subset_right (subset_closure hz))
  have hA := hAmplitude N eps lam θ q sigma [] s hN heps (hsmall.trans_le (min_le_left _ _))
    hl0 hl1 (htl.trans_le (min_le_left _ _)) hθ hSource hAssign (by dsimp [s]; simp; positivity)
  rw [hJ] at hA
  have hR := hRecip η α hη hηsmall hα N eps τ lam θ a q sigma [] s hN heps
    (hsmall.trans_le (min_le_right _ _)) hτ.le hl0 hl1 (htl.trans_le (min_le_right _ _))
    hθ hσa (hσ q) hAssign (by dsimp [s]; simp; positivity)
  simp only [hJ] at hR
  have hRj := left_compact_reciprocal_jet_attach hN q s (deformedPoint f r τ lam θ) hdom.2.2.1
    (fun i => deformedPoint_nonzero f (Real.exp_pos _).ne' τ lam θ i) hW order hB.le hR
  have hNorm : ‖mixedDensityNormalization f τ lam θ‖≤H^N :=
    mixedDensityNormalization_norm_le f τ lam θ hH.le (hJac N (by omega) lam hl0 hl1 θ)
  have hw : ‖currentMixedWeight f d.thetaB outer inner ho hi q qA sigma τ θ‖≤(M*L)^N := by
    have hrw : ‖((namedSelectorDerivative f q θ*nestedSectorWeight d.thetaB outer inner ho hi qA sigma θ):ℝ)‖≤L^N :=
      (hCut N qA sigma [] (by simp) θ).2.2 q
    have hm : 2*τ≤M^N := mixed_constant_le_exponential (2*τ) hN
    have hcτ : ‖(-2*Complex.I*(τ:ℂ))‖=2*τ := by simp [abs_of_pos hτ]
    rw [currentMixedWeight,norm_mul,hcτ,Complex.norm_real,mul_pow]
    exact mul_le_mul hm hrw (norm_nonneg _) (pow_nonneg hM.le N)
  exact compact_weighted_density_gaussian_bound hN q f (Real.exp_pos _) τ lam s θ hdom.2.2.1 hW order k hk
    _ hC.le hB.le hH.le (mul_nonneg hM.le (zero_le_one.trans hL)) hA hRj hNorm hw

end
end IsingBulk.Tail
