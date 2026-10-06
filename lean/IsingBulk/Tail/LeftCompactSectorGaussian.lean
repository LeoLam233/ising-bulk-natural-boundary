import IsingBulk.Tail.LeftCompactCurrentPointwise
import IsingBulk.Tail.LeftCompactKernelIntegral
import IsingBulk.Tail.MixedSectorIntegralIdentity
import IsingBulk.Tail.WeightedAngularJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem originalSectorIntegral_direct_jets {N : ℕ} (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner)
    (q : Fin N) (sigma : Fin N → Fin 3) (k : ℕ) {s : ℂ} (hs : s∈dampingDomain r) :
    iteratedDeriv k (originalSectorIntegral N f r τ b outer inner ho hi (some (q,sigma))) s=
      ∫ θ in angleBox N,originalMixedWeight f b outer inner ho hi q sigma θ*
        iteratedDeriv k (fun z => pulledDensity f r τ 0 z θ) s := by
  rw [originalSectorIntegral_mixed_weight]
  exact (weightedAngularIntegral_jets N hN f hf hr hr1 hτ le_rfl _
    (originalMixedWeight_smooth f hf b outer inner ho hi q sigma).continuous s hs k).1

theorem currentSectorIntegral_direct_jets {N : ℕ} (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) (hl : 0≤lam) (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner)
    (q qA : Fin N) (sigma : Fin N → Fin 3) (k : ℕ) {s : ℂ} (hs : s∈dampingDomain r) :
    iteratedDeriv k (currentSectorIntegral N f r τ lam q b outer inner ho hi (some (qA,sigma))) s=
      ∫ θ in angleBox N,currentMixedWeight f b outer inner ho hi q qA sigma τ θ*
        iteratedDeriv k (fun z => pulledDensity f r τ lam z θ) s := by
  rw [currentSectorIntegral_mixed_weight]
  exact (weightedAngularIntegral_jets N hN f hf hr hr1 hτ hl _
    (currentMixedWeight_smooth f hf b outer inner ho hi q qA sigma τ).continuous s hs k).1

theorem left_compact_original_sector_gaussian_bound (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ κ : ℝ,0<α₀ ∧ 0<κ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ C : ℝ,0<C ∧ ∀ᶠ H : ℝ in atTop,
      ∀ (N k : ℕ) (τ : ℝ) (a q : Fin N) (sigma : Fin N → Fin 3),
      1≤N → k≤order → 0≤τ → sigma a=0 → (∀ i,sigma i≠2) →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*Real.exp (-H))
      let s := radialParameter d.theta (Real.exp (-H))
      ‖iteratedDeriv k (originalSectorIntegral N f r τ d.thetaB outer inner ho hi (some (q,sigma))) s‖≤
        C^N*(N:ℝ)^(4*order+2)*Real.exp (-κ*(N:ℝ)^2)*(H+1)^2 := by
  obtain ⟨ηP,hηP,hPoint⟩ := left_compact_original_pointwise d hcsmall
  refine ⟨min ηP (Real.sin d.thetaB/4),lt_min hηP (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨α₀,κ,hα₀,hκ,hPoint⟩ := hPoint η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨α₀,κ,hα₀,hκ,?_⟩
  intro α hα hαlt order outer cap ho hcap
  let f := constructedSelector d.thetaB η α
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  obtain ⟨inner₀,hi₀,hicap,hPoint⟩ := hPoint α hα hαlt order outer cap ho hcap
  refine ⟨inner₀,hi₀,hicap,?_⟩
  intro inner hi hinner
  obtain ⟨C,hC,hPoint⟩ := hPoint inner hi hinner
  obtain ⟨K,hK,hBudget⟩ := left_compact_kernel_radial_budget d.c₀ d.c₀_pos
  refine ⟨C*K,mul_pos hC hK,?_⟩
  have ht : Tendsto (fun H : ℝ => Real.exp (-H)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_neg_atTop_nhds_zero,
      Eventually.of_forall (fun H => Real.exp_pos (-H))⟩
  filter_upwards [ht.eventually hPoint,ht.eventually (radial_source_eventually_damping d hcsmall),
    eventually_ge_atTop (0:ℝ),Real.tendsto_exp_neg_atTop_nhds_zero.eventually
      (gt_mem_nhds (one_div_pos.mpr d.c₀_pos))] with H hPoint hdom hH heps
  intro N k τ a q sigma hN hk hτ hσa hσ
  let eps := Real.exp (-H)
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let F := fun θ => originalMixedWeight f d.thetaB outer inner ho hi q sigma θ*
    iteratedDeriv k (fun z => pulledDensity f r τ 0 z θ) s
  have hF : IntegrableOn F (angleBox N) :=
    (weightedAngularIntegral_jets N (by omega) f hf hdom.1 hdom.2.1 hτ le_rfl _
      (originalMixedWeight_smooth f hf d.thetaB outer inner ho hi q sigma).continuous s hdom.2.2 k).2.continuousOn.integrableOn_compact isCompact_Icc
  have ha1 : d.c₀*eps≤1 := by have hh := (lt_div_iff₀ d.c₀_pos).mp heps; dsimp [eps]; nlinarith
  have hh := left_compact_source_kernel_integral hN q f d.c₀_pos (Real.exp_pos _) ha1 hτ le_rfl
    hf.p_nonneg hf.m_le_one F hF (by positivity)
    (fun θ hθ => hPoint N k τ θ a q sigma hN hk hτ hθ hσa hσ)
  dsimp only
  rw [originalSectorIntegral_direct_jets (by omega) f hf hdom.1 hdom.2.1 hτ _ _ _ ho hi q sigma k hdom.2.2]
  calc
    _ ≤ _ := hh
    _ ≤ (C^N*(N:ℝ)^(4*order)*Real.exp (-κ*(N:ℝ)^2))*(K^N*(N:ℝ)^2*(H+1)^2) :=
      mul_le_mul_of_nonneg_left (hBudget N H hN hH) (by positivity)
    _ = _ := by simp only [mul_pow,pow_add]; ring

theorem left_compact_current_sector_gaussian_bound (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ τ₀ : ℝ,0<α₀ ∧ 0<τ₀ ∧ ∀ α τ : ℝ,0<α → α<α₀ → 0<τ → τ<τ₀ →
      ∃ κ : ℝ,0<κ ∧ ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ t C : ℝ,0<t ∧ 0<C ∧ ∀ᶠ H : ℝ in atTop,
      ∀ (N k : ℕ) (lam : ℝ) (a q qA : Fin N) (sigma : Fin N → Fin 3),
      1≤N → k≤order → 0≤lam → lam≤1 → lam*τ<t → sigma a=0 → (∀ i,sigma i≠2) →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*Real.exp (-H))
      let s := radialParameter d.theta (Real.exp (-H))
      ‖iteratedDeriv k (currentSectorIntegral N f r τ lam q d.thetaB outer inner ho hi (some (qA,sigma))) s‖≤
        C^N*(N:ℝ)^(4*order+2)*Real.exp (-κ*(N:ℝ)^2)*(H+1)^2 := by
  obtain ⟨ηP,hηP,hPoint⟩ := left_compact_current_pointwise d hcsmall
  refine ⟨min ηP (Real.sin d.thetaB/4),lt_min hηP (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨α₀,τ₀,hα₀,hτ₀,hPoint⟩ := hPoint η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨α₀,τ₀,hα₀,hτ₀,?_⟩
  intro α τ hα hαlt hτ hτlt
  let f := constructedSelector d.thetaB η α
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  obtain ⟨κ,hκ,hPoint⟩ := hPoint α τ hα hαlt hτ hτlt
  refine ⟨κ,hκ,?_⟩
  intro order outer cap ho hcap
  obtain ⟨inner₀,hi₀,hicap,hPoint⟩ := hPoint order outer cap ho hcap
  refine ⟨inner₀,hi₀,hicap,?_⟩
  intro inner hi hinner
  obtain ⟨t,C,htC,hC,hPoint⟩ := hPoint inner hi hinner
  obtain ⟨K,hK,hBudget⟩ := left_compact_kernel_radial_budget d.c₀ d.c₀_pos
  refine ⟨t,C*K,htC,mul_pos hC hK,?_⟩
  have ht : Tendsto (fun H : ℝ => Real.exp (-H)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨Real.tendsto_exp_neg_atTop_nhds_zero,
      Eventually.of_forall (fun H => Real.exp_pos (-H))⟩
  filter_upwards [ht.eventually hPoint,ht.eventually (radial_source_eventually_damping d hcsmall),
    eventually_ge_atTop (0:ℝ),Real.tendsto_exp_neg_atTop_nhds_zero.eventually
      (gt_mem_nhds (one_div_pos.mpr d.c₀_pos))] with H hPoint hdom hH heps
  intro N k lam a q qA sigma hN hk hl0 hl1 htl hσa hσ
  let eps := Real.exp (-H)
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let F := fun θ => currentMixedWeight f d.thetaB outer inner ho hi q qA sigma τ θ*
    iteratedDeriv k (fun z => pulledDensity f r τ lam z θ) s
  have hF : IntegrableOn F (angleBox N) :=
    (weightedAngularIntegral_jets N (by omega) f hf hdom.1 hdom.2.1 hτ.le hl0 _
      (currentMixedWeight_smooth f hf d.thetaB outer inner ho hi q qA sigma τ).continuous s hdom.2.2 k).2.continuousOn.integrableOn_compact isCompact_Icc
  have ha1 : d.c₀*eps≤1 := by have hh := (lt_div_iff₀ d.c₀_pos).mp heps; dsimp [eps]; nlinarith
  have hh := left_compact_source_kernel_integral hN q f d.c₀_pos (Real.exp_pos _) ha1 hτ.le hl0
    hf.p_nonneg hf.m_le_one F hF (by positivity)
    (fun θ hθ => hPoint N k lam θ a q qA sigma hN hk hl0 hl1 htl hθ hσa hσ)
  dsimp only
  rw [currentSectorIntegral_direct_jets (by omega) f hf hdom.1 hdom.2.1 hτ.le hl0 _ _ _ ho hi q qA sigma k hdom.2.2]
  calc
    _ ≤ _ := hh
    _ ≤ (C^N*(N:ℝ)^(4*order)*Real.exp (-κ*(N:ℝ)^2))*(K^N*(N:ℝ)^2*(H+1)^2) :=
      mul_le_mul_of_nonneg_left (hBudget N H hN hH) (by positivity)
    _ = _ := by simp only [mul_pow,pow_add]; ring

end
end IsingBulk.Tail
