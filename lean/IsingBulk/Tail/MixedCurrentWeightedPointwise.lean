import IsingBulk.Tail.MixedCurrentPointwise

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual Stokes-current multiplier is retained in the literal
density and absorbed into the dimension-exponential constant. -/
theorem mixed_current_weight_pointwise (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ τ₀ : ℝ,0<α₀ ∧ 0<τ₀ ∧ ∀ α τ : ℝ,0<α → α<α₀ → 0<τ → τ<τ₀ →
      ∃ κ : ℝ,0<κ ∧ ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e t₀ C : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ 0<C ∧
      ∀ (n k : ℕ) (eps lam : ℝ) (θ : Fin (n+1) → ℝ) (j q a : Fin (n+1))
        (sigma : Fin (n+1) → Fin 3) (s : ℂ),
      k≤order → 0<eps → eps<e → 0≤lam → lam≤1 → lam*τ<t₀ → θ∈angleBox (n+1) → sigma j=2 →
      θ∈tsupport (fun x => namedSelectorDerivative (constructedSelector d.thetaB η α) q x*
        nestedSectorWeight d.thetaB outer inner ho hi a sigma x) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let J := mixedBranchIndexSet sigma
      ‖((IsingBulk.Lie.lieStep (mixedContourVelocity J j q f r τ lam))^[k]
        (fun z x => currentMixedWeight f d.thetaB outer inner ho hi q a sigma τ x*pulledDensity f r τ lam z x)) s θ‖ ≤
      C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*
        (‖mixedSimpleKernel f r τ lam s θ‖*‖mixedHybridVolume J f r τ lam s θ‖) := by
  obtain ⟨η₀,hη₀,hSetup⟩ := mixed_current_real_weight_pointwise d hcsmall
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηlt
  obtain ⟨α₀,τ₀,hα₀,hτ₀,hSetup⟩ := hSetup η hη hηlt
  refine ⟨α₀,τ₀,hα₀,hτ₀,?_⟩
  intro α τ hα hαlt hτ hτlt
  obtain ⟨κ,hκ,hSetup⟩ := hSetup α τ hα hαlt hτ hτlt
  refine ⟨κ,hκ,?_⟩
  intro order outer cap ho hcap
  obtain ⟨inner₀,hi₀,hicap,hSetup⟩ := hSetup order outer cap ho hcap
  refine ⟨inner₀,hi₀,hicap,?_⟩
  intro inner hi hinner
  obtain ⟨c,e,t₀,C,hc,he,ht,hC,hBound⟩ := hSetup inner hi hinner
  let M := max 1 (2*τ)
  have hM : 1≤M := le_max_left _ _
  have hMpos : 0<M := zero_lt_one.trans_le hM
  refine ⟨c,e,t₀,M*C,hc,he,ht,mul_pos hMpos hC,?_⟩
  intro n k eps lam θ j q a sigma s hk heps hepslt hl0 hl1 htl hθ hσj hsupport hs
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let J := mixedBranchIndexSet sigma
  let w := fun x => namedSelectorDerivative f q x*nestedSectorWeight d.thetaB outer inner ho hi a sigma x
  let cτ : ℂ := -2*Complex.I*(τ:ℂ)
  have hcτ : ‖cτ‖=2*τ := by simp [cτ,abs_of_pos hτ]
  have heq : (fun z x => currentMixedWeight f d.thetaB outer inner ho hi q a sigma τ x*pulledDensity f r τ lam z x)=
      (fun z x => cτ*((w x:ℂ)*pulledDensity f r τ lam z x)) := by
    funext z x
    exact mul_assoc _ _ _
  have hh := hBound n k eps lam θ j q a sigma s hk heps hepslt hl0 hl1 htl hθ hσj hsupport hs
  have hMP : 2*τ≤M^(n+1) := (le_max_right _ _).trans
    (by simpa only [pow_one] using pow_le_pow_right₀ hM (show 1≤n+1 by omega))
  dsimp only
  rw [heq,iterate_lieStep_const_mul,norm_mul,hcτ]
  calc
    _ ≤ (2*τ)*(C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*
        (‖mixedSimpleKernel f r τ lam s θ‖*‖mixedHybridVolume J f r τ lam s θ‖)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ M^(n+1)*(C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*
        (‖mixedSimpleKernel f r τ lam s θ‖*‖mixedHybridVolume J f r τ lam s θ‖)) := by gcongr
    _ = _ := by rw [mul_pow]; ring

end
end IsingBulk.Tail
