import IsingBulk.Tail.MixedCurrentPositiveSupportedIntegral
import IsingBulk.Tail.MixedOriginalPositiveDensity
import IsingBulk.Tail.MixedCurrentWeightedPointwise

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Lie Set MeasureTheory Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The actual current Lie iterate, including its multiplier, has an
integrated positive-half estimate. The Gaussian coefficient is fixed
before the derivative order and the lambda bound is uniform. -/
theorem mixed_current_positive_density_integral (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ : ℝ,0<α₀ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∃ τ₀ : ℝ,0<τ₀ ∧ ∀ τ : ℝ,0<τ → τ<τ₀ →
      ∃ κ : ℝ,0<κ ∧ ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ (e t C a B : ℝ) (M : ℕ),0<e ∧ 0<t ∧ 0<C ∧ 0<a ∧ 0<B ∧
      ∀ (n k : ℕ) (eps lam : ℝ) (j q qA : Fin (n+1)) (sigma : Fin (n+1) → Fin 3),
      k≤order → 0<eps → eps<e → 0≤lam → lam≤1 → lam*τ<t → sigma j=2 → sigma q≠2 →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let s := radialParameter d.theta eps
      let F := ((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ lam))^[k]
        (fun z θ => currentMixedWeight f d.thetaB outer inner ho hi q qA sigma τ θ*pulledDensity f r τ lam z θ)) s
      (∫ θ in mixedPositiveAngularHalf d.thetaB j,‖F θ‖)≤
        (C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2))*
          ((M:ℝ)*mixedPositiveIntegralBudget (n+1) (d.c₀*eps) (a*eps)
            (2*Real.pi+4*B*Real.sqrt (2*Real.pi))) := by
  obtain ⟨ηP,hηP,hPoint⟩ := mixed_current_weight_pointwise d hcsmall
  refine ⟨min ηP (Real.sin d.thetaB/4),lt_min hηP (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨αP,τP,hαP,hτP,hPoint⟩ := hPoint η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αP (Real.sin d.thetaB/4),lt_min hαP (by positivity [d.a_pos]),?_⟩
  intro α hα hαlt
  have hαsmall := hαlt.trans_le (min_le_right _ _)
  obtain ⟨iG,τG,B,M,hiG,hτG,hB,hIntegral⟩ := mixed_current_positive_supported_integral d hcsmall
    η α hη hηsmall hα hαsmall
  refine ⟨min τP τG,lt_min hτP hτG,?_⟩
  intro τ hτ hτlt
  obtain ⟨κ,hκ,hPoint⟩ := hPoint α τ hα (hαlt.trans_le (min_le_left _ _)) hτ (hτlt.trans_le (min_le_left _ _))
  obtain ⟨a,eG,ha,heG,hIntegral⟩ := hIntegral τ hτ.le (hτlt.trans_le (min_le_right _ _))
  refine ⟨κ,hκ,?_⟩
  intro order outer cap ho hcap
  obtain ⟨iP,hiP,hiPcap,hPoint⟩ := hPoint order outer (min cap iG) ho (lt_min hcap hiG)
  obtain ⟨iL,hiL,_hiLcap,hLie⟩ := current_mixed_sector_lie_integral d hcsmall cap hcap
  refine ⟨min iP iL,lt_min hiP hiL,(min_le_left _ _).trans (hiPcap.trans (min_le_left _ _)),?_⟩
  intro inner hi hinner
  obtain ⟨cP,eP,tP,C,hcP,heP,htP,hC,hPoint⟩ := hPoint inner hi (hinner.trans (min_le_left _ _))
  obtain ⟨cL,eL,tL,hcL,_hcL1,heL,htL,hLie⟩ := hLie inner hi (hinner.trans (min_le_right _ _))
  refine ⟨min eG (min eP eL),min tP tL,C,a,B,M,
    lt_min heG (lt_min heP heL),lt_min htP htL,hC,ha,hB,?_⟩
  intro n k eps lam j q qA sigma hk he heSmall hl0 hl1 htl hσj hσq
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let F := ((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ lam))^[k]
    (fun z θ => currentMixedWeight f d.thetaB outer inner ho hi q qA sigma τ θ*pulledDensity f r τ lam z θ)) s
  have hid := hLie η α hη hηsmall hα hαsmall outer ho n eps τ lam j q qA sigma he
    (heSmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hτ.le hl0 hl1
    (htl.trans_le (min_le_right _ _)) hσj
  have hF : IntegrableOn F (angleBox (n+1)) := (hid k).2 s (by dsimp [s]; simp; positivity)
  apply hIntegral inner hi ((hinner.trans (min_le_left _ _)).trans (hiPcap.trans (min_le_right _ _))) outer ho
    (n+1) j q qA sigma eps lam (C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)) F
    hσj hσq he (heSmall.trans_le (min_le_left _ _)) hl0 hl1 (by positivity) hF
    (current_mixed_iterate_support f d.thetaB outer inner ho hi j q qA sigma r τ lam k s)
  intro θ hθ hK
  exact hPoint n k eps lam θ j q qA sigma s hk he
    (heSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hl0 hl1
    (htl.trans_le (min_le_left _ _)) hθ hσj hK (by dsimp [s]; simp; positivity)

end
end IsingBulk.Tail
