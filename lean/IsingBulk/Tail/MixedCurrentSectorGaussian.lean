import IsingBulk.Tail.MixedCurrentPositiveDensity
import IsingBulk.Tail.MixedCurrentNegativeDensity
import IsingBulk.Tail.MixedSignedIntegral
import IsingBulk.Tail.MixedGaussianIntegralBudget
import IsingBulk.Tail.MixedSectorIntegralIdentity

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Lie Set MeasureTheory Metric Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The full current-sector derivative estimate, with the actual current
multiplier and a cutoff uniform in lambda, particle number and order. -/
theorem mixed_current_sector_gaussian_bound (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ : ℝ,0<α₀ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∃ τ₀ : ℝ,0<τ₀ ∧ ∀ τ : ℝ,0<τ → τ<τ₀ →
      ∃ κ : ℝ,0<κ ∧ ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ t C : ℝ,0<t ∧ 0<C ∧ ∀ᶠ H : ℝ in atTop,
      ∀ (n k : ℕ) (lam : ℝ) (j q qA : Fin (n+1)) (sigma : Fin (n+1) → Fin 3),
      k≤order → 0≤lam → lam≤1 → lam*τ<t → sigma j=2 → sigma q≠2 →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*Real.exp (-H))
      let s := radialParameter d.theta (Real.exp (-H))
      ‖iteratedDeriv k (currentSectorIntegral (n+1) f r τ lam q d.thetaB outer inner ho hi (some (qA,sigma))) s‖≤
        C^(n+1)*((n+1:ℕ):ℝ)^(5*order+2)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*(H+1)^2 := by
  obtain ⟨ηP,hηP,hPositive⟩ := mixed_current_positive_density_integral d hcsmall
  obtain ⟨ηN,hηN,hNegative⟩ := mixed_current_negative_density_integral d hcsmall
  refine ⟨min ηP (min ηN (Real.sin d.thetaB/4)),lt_min hηP (lt_min hηN (by positivity [d.a_pos])),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨αP,hαP,hPositive⟩ := hPositive η hη (hηlt.trans_le (min_le_left _ _))
  obtain ⟨αN,hαN,hNegative⟩ := hNegative η hη
    (hηlt.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  refine ⟨min αP (min αN (Real.sin d.thetaB/4)),
    lt_min hαP (lt_min hαN (by positivity [d.a_pos])),?_⟩
  intro α hα hαlt
  have hαsmall := hαlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨τP,hτP,hPositive⟩ := hPositive α hα (hαlt.trans_le (min_le_left _ _))
  obtain ⟨τN,hτN,hNegative⟩ := hNegative α hα
    (hαlt.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  refine ⟨min τP τN,lt_min hτP hτN,?_⟩
  intro τ hτ hτlt
  obtain ⟨κP,hκP,hPositive⟩ := hPositive τ hτ (hτlt.trans_le (min_le_left _ _))
  obtain ⟨κN,hκN,hNegative⟩ := hNegative τ hτ (hτlt.trans_le (min_le_right _ _))
  refine ⟨min κP κN,lt_min hκP hκN,?_⟩
  intro order outer cap ho hcap
  obtain ⟨iP,hiP,hiPcap,hPositive⟩ := hPositive order outer cap ho hcap
  obtain ⟨iN,hiN,_hiNcap,hNegative⟩ := hNegative order outer cap ho hcap
  obtain ⟨iL,hiL,_hiLcap,hLie⟩ := current_mixed_sector_lie_integral d hcsmall cap hcap
  refine ⟨min iP (min iN iL),lt_min hiP (lt_min hiN hiL),(min_le_left _ _).trans hiPcap,?_⟩
  intro inner hi hinner
  obtain ⟨eP,tP,CP,a,BP,M,hEP,htP,hCP,ha,hBP,hPositive⟩ := hPositive inner hi (hinner.trans (min_le_left _ _))
  obtain ⟨eN,tN,CN,KN,BN,hEN,htN,hCN,hKN,hBN,hNegative⟩ := hNegative inner hi
    (hinner.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨cL,eL,tL,hcL,_hcL1,heL,htL,hLie⟩ := hLie inner hi
    (hinner.trans ((min_le_right _ _).trans (min_le_right _ _)))
  let PP := 2*Real.pi+4*BP*Real.sqrt (2*Real.pi)
  let PN := 2*Real.pi+4*BN*Real.sqrt (2*Real.pi)
  obtain ⟨KP,hKP,hBudgetP⟩ := mixed_positive_kernel_radial_budget d.c₀ a PP d.c₀_pos ha (by dsimp [PP]; positivity)
  obtain ⟨KG,hKG,hBudgetN⟩ := mixed_negative_kernel_radial_budget d.c₀ PN d.c₀_pos (by dsimp [PN]; positivity)
  let A := CP*max 1 (M:ℝ)*KP
  let B := CN*max 1 KN*KG
  have hA : 0<A := mul_pos (mul_pos hCP (zero_lt_one.trans_le (le_max_left _ _))) hKP
  have hB : 0<B := mul_pos (mul_pos hCN (zero_lt_one.trans_le (le_max_left _ _))) hKG
  refine ⟨min tP (min tN tL),2*max A B,lt_min htP (lt_min htN htL),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (0:ℝ),
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (lt_min hEP (lt_min hEN heL)))] with H hH heps
  intro n k lam j q qA sigma hk hl0 hl1 htl hσj hσq
  let eps := Real.exp (-H)
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  let F := ((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ lam))^[k]
    (fun z θ => currentMixedWeight f d.thetaB outer inner ho hi q qA sigma τ θ*pulledDensity f r τ lam z θ)) s
  have hid := hLie η α hη hηsmall hα hαsmall outer ho n eps τ lam j q qA sigma (Real.exp_pos _)
    (heps.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hτ.le hl0 hl1
    (htl.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hσj
  have hs : s∈ball (radialParameter d.theta eps) (cL*eps) := by dsimp [s]; simp; positivity [Real.exp_pos (-H)]
  have hF : IntegrableOn F (angleBox (n+1)) := (hid k).2 s hs
  have hP := hPositive n k eps lam j q qA sigma hk (Real.exp_pos _) (heps.trans_le (min_le_left _ _))
    hl0 hl1 (htl.trans_le (min_le_left _ _)) hσj hσq
  have hN := hNegative n k eps lam j q qA sigma hk (Real.exp_pos _)
    (heps.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hl0 hl1
    (htl.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hσj hσq
  have hPc := mixed_density_radial_cost_bound (order := order) (κ := κP) hCP.le
    (Nat.cast_nonneg M) hKP.le (by omega : 1≤n+1) (hBudgetP (n+1) H (by omega) hH)
  have hNc := mixed_density_radial_cost_bound (order := order) (κ := κN) hCN.le
    hKN.le hKG.le (by omega : 1≤n+1) (hBudgetN (n+1) H (by omega) hH)
  have hh := mixed_norm_integral_le_signed_halves d.thetaB j F hF (hP.trans hPc) (hN.trans hNc)
  dsimp only
  rw [currentSectorIntegral_lie_iterate f r τ lam d.thetaB outer inner ho hi j q qA sigma hid k hs]
  exact hh.trans (mixed_gaussian_bounds_add hA.le hB.le (by omega))

end
end IsingBulk.Tail
