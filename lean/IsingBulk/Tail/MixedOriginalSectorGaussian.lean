import IsingBulk.Tail.MixedOriginalPositiveDensity
import IsingBulk.Tail.MixedOriginalNegativeDensity
import IsingBulk.Tail.MixedSignedIntegral
import IsingBulk.Tail.MixedGaussianIntegralBudget
import IsingBulk.Tail.MixedSectorIntegralIdentity

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Lie Set MeasureTheory Metric Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Full original separated mixed-sector derivative estimate. Both sign
halves use one inner width and one eventual radial cutoff, uniform in
particle number, labelled sector and all derivative orders up to order. -/
theorem mixed_original_sector_gaussian_bound (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ κ : ℝ,0<α₀ ∧ 0<κ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ C : ℝ,0<C ∧ ∀ᶠ H : ℝ in atTop,
      ∀ (n k : ℕ) (τ : ℝ) (j q : Fin (n+1)) (sigma : Fin (n+1) → Fin 3),
      k≤order → 0≤τ → sigma j=2 → sigma q≠2 →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*Real.exp (-H))
      let s := radialParameter d.theta (Real.exp (-H))
      ‖iteratedDeriv k (originalSectorIntegral (n+1) f r τ d.thetaB outer inner ho hi (some (q,sigma))) s‖≤
        C^(n+1)*((n+1:ℕ):ℝ)^(5*order+2)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*(H+1)^2 := by
  obtain ⟨ηP,hηP,hPositive⟩ := mixed_original_positive_density_integral d hcsmall
  obtain ⟨ηN,hηN,hNegative⟩ := mixed_original_negative_density_integral d hcsmall
  refine ⟨min ηP (min ηN (Real.sin d.thetaB/4)),lt_min hηP (lt_min hηN (by positivity [d.a_pos])),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨αP,κP,hαP,hκP,hPositive⟩ := hPositive η hη (hηlt.trans_le (min_le_left _ _))
  obtain ⟨αN,κN,hαN,hκN,hNegative⟩ := hNegative η hη
    (hηlt.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  refine ⟨min αP (min αN (Real.sin d.thetaB/4)),min κP κN,
    lt_min hαP (lt_min hαN (by positivity [d.a_pos])),lt_min hκP hκN,?_⟩
  intro α hα hαlt order outer cap ho hcap
  have hαsmall := hαlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨iP,hiP,hiPcap,hPositive⟩ := hPositive α hα (hαlt.trans_le (min_le_left _ _)) order outer cap ho hcap
  obtain ⟨iN,hiN,_hiNcap,hNegative⟩ := hNegative α hα
    (hαlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))) order outer cap ho hcap
  obtain ⟨iL,hiL,_hiLcap,hLie⟩ := original_mixed_sector_lie_integral d hcsmall outer ho cap hcap
  refine ⟨min iP (min iN iL),lt_min hiP (lt_min hiN hiL),(min_le_left _ _).trans hiPcap,?_⟩
  intro inner hi hinner
  obtain ⟨eP,CP,a,BP,M,hEP,hCP,ha,hBP,hPositive⟩ := hPositive inner hi (hinner.trans (min_le_left _ _))
  obtain ⟨eN,CN,KN,BN,hEN,hCN,hKN,hBN,hNegative⟩ := hNegative inner hi
    (hinner.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨cL,eL,hcL,_hcL1,heL,hLie⟩ := hLie inner hi
    (hinner.trans ((min_le_right _ _).trans (min_le_right _ _)))
  let PP := 2*Real.pi+4*BP*Real.sqrt (2*Real.pi)
  let PN := 2*Real.pi+4*BN*Real.sqrt (2*Real.pi)
  obtain ⟨KP,hKP,hBudgetP⟩ := mixed_positive_kernel_radial_budget d.c₀ a PP d.c₀_pos ha (by dsimp [PP]; positivity)
  obtain ⟨KG,hKG,hBudgetN⟩ := mixed_negative_kernel_radial_budget d.c₀ PN d.c₀_pos (by dsimp [PN]; positivity)
  let A := CP*max 1 (M:ℝ)*KP
  let B := CN*max 1 KN*KG
  have hA : 0<A := mul_pos (mul_pos hCP (zero_lt_one.trans_le (le_max_left _ _))) hKP
  have hB : 0<B := mul_pos (mul_pos hCN (zero_lt_one.trans_le (le_max_left _ _))) hKG
  refine ⟨2*max A B,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (0:ℝ),
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (lt_min hEP (lt_min hEN heL)))] with H hH heps
  intro n k τ j q sigma hk hτ hσj hσq
  let eps := Real.exp (-H)
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let F := ((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ 0))^[k]
    (fun z θ => originalMixedWeight f d.thetaB outer inner ho hi q sigma θ*pulledDensity f r τ 0 z θ)) s
  have hid := hLie η α hη hηsmall hα hαsmall n eps τ j q sigma (Real.exp_pos _)
    (heps.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hτ hσj
  have hs : s∈ball (radialParameter d.theta eps) (cL*eps) := by dsimp [s]; simp; positivity [Real.exp_pos (-H)]
  have hF : IntegrableOn F (angleBox (n+1)) := (hid k).2 s hs
  have hP := hPositive n k eps τ j q sigma hk (Real.exp_pos _) (heps.trans_le (min_le_left _ _)) hτ hσj hσq
  have hN := hNegative n k eps τ j q sigma hk (Real.exp_pos _)
    (heps.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hτ hσj hσq
  have hPc := mixed_density_radial_cost_bound (order := order) (κ := κP) hCP.le
    (Nat.cast_nonneg M) hKP.le (by omega : 1≤n+1) (hBudgetP (n+1) H (by omega) hH)
  have hNc := mixed_density_radial_cost_bound (order := order) (κ := κN) hCN.le
    hKN.le hKG.le (by omega : 1≤n+1) (hBudgetN (n+1) H (by omega) hH)
  have hh := mixed_norm_integral_le_signed_halves d.thetaB j F hF (hP.trans hPc) (hN.trans hNc)
  dsimp only
  rw [originalSectorIntegral_lie_iterate f r τ d.thetaB outer inner ho hi j q sigma hid k hs]
  exact hh.trans (mixed_gaussian_bounds_add hA.le hB.le (by omega))

end
end IsingBulk.Tail
