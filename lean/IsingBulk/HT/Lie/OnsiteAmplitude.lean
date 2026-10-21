import IsingBulk.Tail.MixedActiveSourceGerm
import IsingBulk.HT.Lie.OnsiteSource

/-! The actual onsite analytic amplitude uses the product of both inverse
coordinate products. Its finite jets are constructed from the same regular
one-body factors, rather than bounded by the offsite sum of inverse products. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Jets IsingBulk.HT.Contour Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

def onsiteActiveSmoothAmplitude {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (u : MixedActiveSpace N) : ℂ :=
  (∏ i,mixedActiveAmplitudeVertex J q s φ y 1 i u)*
    (∏ i,mixedActiveAmplitudeVertex J q s φ y 2 i u)*
    ∏ i,mixedActiveAmplitudeVertex J q s φ y 0 i u

def onsiteActiveRegularAmplitude {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (u : MixedActiveSpace N) : ℂ :=
  onsiteActiveSmoothAmplitude J q s φ y u*mixedActivePairProduct J q s φ y u

theorem onsiteActiveSmoothAmplitude_source {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hsin : ∀ i∈J,Real.sin (θ i)<0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    onsiteActiveSmoothAmplitude J q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ) 0=
      (coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i))*
        coordinateProduct (deformedPoint f r τ lam θ))⁻¹*
        ∏ i,mixedSourceOneBody J f r τ lam s θ i := by
  unfold onsiteActiveSmoothAmplitude
  simp_rw [mixedActiveAmplitudeVertex_onebody_source J q f r τ lam s θ _ (hW _),
    mixedActiveAmplitudeVertex_inverse_root_source J q f r τ lam s θ _ (hW _),
    mixedActiveAmplitudeVertex_inverse_y_source J q f hr τ lam s θ _ (hsin _)]
  simp only [coordinateProduct,Finset.prod_inv_distrib,mul_inv_rev]
  ring

theorem onsiteActiveRegularAmplitude_source {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hsin : ∀ i∈J,Real.sin (θ i)<0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    onsitePulledDensity f r τ lam s θ=
      (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
        (angularJacobian f τ lam θ).det*mixedHybridVolume J f r τ lam s θ*
        onsiteActiveRegularAmplitude J q s
          (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
          (deformedPoint f r τ lam θ) 0 := by
  rw [onsite_pulled_density_hybrid_factorization J f hr τ lam s θ hsin (fun i _ => hW i)]
  unfold onsiteActiveRegularAmplitude onsiteHybridAmplitude
  rw [onsiteActiveSmoothAmplitude_source J q f hr τ lam s θ hsin hW,
    mixedActivePairProduct_source J q f hr τ lam s θ hsin hW]
  dsimp only
  ring

/-- The dimension loss is polynomial of degree equal to the jet order.
All three vertex families are multiplied, with no division by a source pair. -/
theorem onsiteActiveSmoothAmplitude_jets {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (order : ℕ) {C : ℝ} (hC : 0≤C)
    (hf : ∀ a i,JetBound (mixedActiveAmplitudeVertex J q s φ y a i) 0 order C) :
    AnalyticAt ℂ (onsiteActiveSmoothAmplitude J q s φ y) 0 ∧ ∀ k≤order,
      ‖iteratedFDeriv ℂ k (onsiteActiveSmoothAmplitude J q s φ y) 0‖≤
        2*(2^order*(2^order*C*C)*C)^N*(N:ℝ)^k := by
  let g := fun i : Fin N => fun u : MixedActiveSpace N =>
    mixedActiveAmplitudeVertex J q s φ y 1 i u*
      mixedActiveAmplitudeVertex J q s φ y 2 i u*
      mixedActiveAmplitudeVertex J q s φ y 0 i u
  have hg (i : Fin N) : JetBound (g i) 0 order (2^order*(2^order*C*C)*C) :=
    ((hf 1 i).mul (hf 2 i)).mul (hf 0 i)
  have he : onsiteActiveSmoothAmplitude J q s φ y = fun u => ∏ i,g i u := by
    funext u
    simp only [onsiteActiveSmoothAmplitude,g,Finset.prod_mul_distrib]
  rw [he]
  refine ⟨Finset.analyticAt_fun_prod _ (fun i _ => (hg i).analytic),?_⟩
  intro k hk
  have hh := analytic_finset_product_geometric_jets Finset.univ g 0 order
    (2^order*(2^order*C*C)*C) 1 (by positivity) (by norm_num)
    (fun i _ => (hg i).analytic) (fun i _ l hl => by simpa using (hg i).bound l hl) k hk
  have hb : ‖iteratedFDeriv ℂ k (fun u => ∏ i,g i u) 0‖ ≤
      (2^order*(2^order*C*C)*C)^N*(N:ℝ)^k := by simpa using hh
  exact hb.trans (by nlinarith [show 0≤(2^order*(2^order*C*C)*C)^N*(N:ℝ)^k by positivity])

theorem onsite_actual_smooth_amplitude_jets (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) (order : ℕ) :
    ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e t₀ B : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ 0<B ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ → θ∈angleBox N →
      θ∈tsupport (cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
      let φ := fun i => mixedSourcePhase s (y i)
      let F := onsiteActiveSmoothAmplitude (mixedBranchIndexSet sigma) q s φ y
      AnalyticAt ℂ F 0 ∧ ∀ k≤order,‖iteratedFDeriv ℂ k F 0‖≤2*B^N*(N:ℝ)^k := by
  obtain ⟨inner₀,hi₀,hicap,hVertex⟩ := mixed_actual_amplitude_vertex_jets d hcsmall cap hcap order
  refine ⟨inner₀,hi₀,hicap,?_⟩
  intro inner hi hinner
  obtain ⟨c,e,t₀,C,hc,he,ht,hC,hVertex⟩ := hVertex inner hi hinner
  refine ⟨c,e,t₀,2^order*(2^order*C*C)*C,hc,he,ht,by positivity,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ q sigma l s hN heps hepslt hτ hl0 hl1 htl hθ hsupp hs
  exact onsiteActiveSmoothAmplitude_jets (mixedBranchIndexSet sigma) q s _ _ order hC.le
    (hVertex η α hη hηsmall hα N eps τ lam θ q sigma l s hN heps hepslt hτ hl0 hl1 htl hθ hsupp hs)

end
end IsingBulk.HT.Lie
