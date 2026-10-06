import IsingBulk.Tail.MixedNegativeSupportedIntegral
import IsingBulk.Tail.MixedOriginalPositiveDensity

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Lie Set MeasureTheory Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem mixed_original_negative_density_integral (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ κ : ℝ,0<α₀ ∧ 0<κ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ e C K B : ℝ,0<e ∧ 0<C ∧ 0<K ∧ 0<B ∧
      ∀ (n k : ℕ) (eps τ : ℝ) (j q : Fin (n+1)) (sigma : Fin (n+1) → Fin 3),
      k≤order → 0<eps → eps<e → 0≤τ → sigma j=2 → sigma q≠2 →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let s := radialParameter d.theta eps
      let F := ((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ 0))^[k]
        (fun z θ => originalMixedWeight f d.thetaB outer inner ho hi q sigma θ*pulledDensity f r τ 0 z θ)) s
      (∫ θ in mixedNegativeAngularHalf d.thetaB j,‖F θ‖)≤
        (C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2))*
          (K*mixedNegativeIntegralBudget (n+1) (d.c₀*eps) eps
            (2*Real.pi+4*B*Real.sqrt (2*Real.pi))) := by
  obtain ⟨ηP,hηP,hPoint⟩ := mixed_original_weight_pointwise d hcsmall
  refine ⟨min ηP (Real.sin d.thetaB/4),lt_min hηP (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨αP,κ,hαP,hκ,hPoint⟩ := hPoint η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αP (Real.sin d.thetaB/4),κ,lt_min hαP (by positivity [d.a_pos]),hκ,?_⟩
  intro α hα hαlt order outer cap ho hcap
  have hαsmall := hαlt.trans_le (min_le_right _ _)
  obtain ⟨iG,eG,tG,K,B,hiG,heG,_htG,hK,hB,hIntegral⟩ := mixed_negative_supported_integral d hcsmall
    η α hη hηsmall hα hαsmall
  obtain ⟨iP,hiP,hiPcap,hPoint⟩ := hPoint α hα (hαlt.trans_le (min_le_left _ _)) order outer
    (min cap iG) ho (lt_min hcap hiG)
  obtain ⟨iL,hiL,_hiLcap,hLie⟩ := original_mixed_sector_lie_integral d hcsmall outer ho cap hcap
  refine ⟨min iP iL,lt_min hiP hiL,(min_le_left _ _).trans (hiPcap.trans (min_le_left _ _)),?_⟩
  intro inner hi hinner
  obtain ⟨cP,eP,C,hcP,heP,hC,hPoint⟩ := hPoint inner hi (hinner.trans (min_le_left _ _))
  obtain ⟨cL,eL,hcL,_hcL1,heL,hLie⟩ := hLie inner hi (hinner.trans (min_le_right _ _))
  refine ⟨min eG (min eP eL),C,K,B,lt_min heG (lt_min heP heL),hC,hK,hB,?_⟩
  intro n k eps τ j q sigma hk he heSmall hτ hσj hσq
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let J := mixedBranchIndexSet sigma
  let S := tsupport (fun θ => angularSelector f θ*nestedSectorWeight d.thetaB outer inner ho hi q sigma θ)
  let F := ((lieStep (mixedContourVelocity J j q f r τ 0))^[k]
    (fun z θ => originalMixedWeight f d.thetaB outer inner ho hi q sigma θ*pulledDensity f r τ 0 z θ)) s
  have hid := hLie η α hη hηsmall hα hαsmall n eps τ j q sigma he
    (heSmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hτ hσj
  have hF : IntegrableOn F (angleBox (n+1)) := (hid k).2 s (by dsimp [s]; simp; positivity)
  apply hIntegral inner hi ((hinner.trans (min_le_left _ _)).trans (hiPcap.trans (min_le_right _ _)))
    (n+1) J j q eps τ 0 (C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)) F S
    (by simp [J,mixedBranchIndexSet,hσj]) (by simpa [J,mixedBranchIndexSet] using hσq)
    he (heSmall.trans_le (min_le_left _ _)) hτ (Or.inl rfl) le_rfl zero_le_one (by positivity) hF
    (original_mixed_iterate_support f d.thetaB outer inner ho hi j q sigma r τ k s)
    (fun _ _ hS => Or.inl (tsupport_mul_subset_left hS))
    (fun _ _ hS => nested_sector_branch_support d.thetaB outer inner ho hi q sigma (tsupport_mul_subset_right hS))
  intro θ hθ hS
  exact hPoint n k eps τ θ j q sigma s hk he
    (heSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hτ hθ hσj hS (by dsimp [s]; simp; positivity)

end
end IsingBulk.Tail
