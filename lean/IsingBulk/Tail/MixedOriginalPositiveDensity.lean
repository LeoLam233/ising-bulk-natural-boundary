import IsingBulk.Tail.MixedPositiveSupportedIntegral
import IsingBulk.Tail.MixedIterateSourceSupport

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Lie Set MeasureTheory Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Actual all-order original mixed Lie density, integrated on the
positive branch half. All pointwise and integration inputs are internal;
the Gaussian coefficient is chosen before the derivative order. -/
theorem mixed_original_positive_density_integral (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ κ : ℝ,0<α₀ ∧ 0<κ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ (e C a B : ℝ) (M : ℕ),0<e ∧ 0<C ∧ 0<a ∧ 0<B ∧
      ∀ (n k : ℕ) (eps τ : ℝ) (j q : Fin (n+1)) (sigma : Fin (n+1) → Fin 3),
      k≤order → 0<eps → eps<e → 0≤τ → sigma j=2 → sigma q≠2 →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let s := radialParameter d.theta eps
      let F := ((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ 0))^[k]
        (fun z θ => originalMixedWeight f d.thetaB outer inner ho hi q sigma θ*pulledDensity f r τ 0 z θ)) s
      (∫ θ in mixedPositiveAngularHalf d.thetaB j,‖F θ‖)≤
        (C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2))*
          ((M:ℝ)*mixedPositiveIntegralBudget (n+1) (d.c₀*eps) (a*eps)
            (2*Real.pi+4*B*Real.sqrt (2*Real.pi))) := by
  obtain ⟨ηP,hηP,hPoint⟩ := mixed_original_weight_pointwise d hcsmall
  refine ⟨min ηP (Real.sin d.thetaB/4),lt_min hηP (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨αP,κ,hαP,hκ,hPoint⟩ := hPoint η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αP (Real.sin d.thetaB/4),κ,lt_min hαP (by positivity [d.a_pos]),hκ,?_⟩
  intro α hα hαlt order outer cap ho hcap
  have hαsmall := hαlt.trans_le (min_le_right _ _)
  obtain ⟨iG,eG,a,B,M,hiG,heG,ha,hB,hIntegral⟩ := mixed_original_positive_supported_integral d hcsmall
    η α outer ho hη hηsmall hα hαsmall
  obtain ⟨iP,hiP,hiPcap,hPoint⟩ := hPoint α hα (hαlt.trans_le (min_le_left _ _)) order outer
    (min cap iG) ho (lt_min hcap hiG)
  obtain ⟨iL,hiL,_hiLcap,hLie⟩ := original_mixed_sector_lie_integral d hcsmall outer ho cap hcap
  refine ⟨min iP iL,lt_min hiP hiL,(min_le_left _ _).trans (hiPcap.trans (min_le_left _ _)),?_⟩
  intro inner hi hinner
  obtain ⟨cP,eP,C,hcP,heP,hC,hPoint⟩ := hPoint inner hi (hinner.trans (min_le_left _ _))
  obtain ⟨cL,eL,hcL,_hcL1,heL,hLie⟩ := hLie inner hi (hinner.trans (min_le_right _ _))
  refine ⟨min eG (min eP eL),C,a,B,M,lt_min heG (lt_min heP heL),hC,ha,hB,?_⟩
  intro n k eps τ j q sigma hk he heSmall hτ hσj hσq
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let F := ((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ 0))^[k]
    (fun z θ => originalMixedWeight f d.thetaB outer inner ho hi q sigma θ*pulledDensity f r τ 0 z θ)) s
  have hid := hLie η α hη hηsmall hα hαsmall n eps τ j q sigma he
    (heSmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hτ hσj
  have hF : IntegrableOn F (angleBox (n+1)) := (hid k).2 s (by dsimp [s]; simp; positivity)
  apply hIntegral inner hi ((hinner.trans (min_le_left _ _)).trans (hiPcap.trans (min_le_right _ _)))
    (n+1) j q sigma eps τ (C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)) F
    hσj hσq he (heSmall.trans_le (min_le_left _ _)) (by positivity) hF
    (original_mixed_iterate_support f d.thetaB outer inner ho hi j q sigma r τ k s)
  intro θ hθ hK
  exact hPoint n k eps τ θ j q sigma s hk he
    (heSmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hτ hθ hσj hK (by dsimp [s]; simp; positivity)

end
end IsingBulk.Tail
