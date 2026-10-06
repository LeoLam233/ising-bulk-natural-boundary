import IsingBulk.Tail.CompactDiameterIntegral
import IsingBulk.Tail.MixedKernelRadialBudget

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set Filter MeasureTheory
open scoped Topology BigOperators
set_option maxHeartbeats 1500000

def compactDiameterIntegralBudget (N : ℕ) (C R a b : ℝ) : ℝ :=
  (N:ℝ)^2*(C*(((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
    ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*(2*R)^(N-2)))

theorem compact_diameter_kernel_radial_budget {C R c a : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hc : 0 < c) (ha : 0 < a) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (H : ℝ), 1 ≤ N → 0 ≤ H →
      compactDiameterIntegralBudget N C R (c*Real.exp (-H)) (a*Real.exp (-H)) ≤
        K^N*(N:ℝ)^4*(H+1)^2 := by
  let A := C*simpleKernelConstant^2*(1+|Real.log c|)*(1+|Real.log a|)
  let K := max 1 A*max 1 (2*R)
  have hsk := simpleKernelConstant_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 < K := mul_pos (zero_lt_one.trans_le (le_max_left _ _))
    (zero_lt_one.trans_le (le_max_left _ _))
  refine ⟨K,hK,?_⟩
  intro N H hN hH
  have hcLog := allBranchExterior_radial_log_factor c H hc hH
  have haLog := allBranchExterior_radial_log_factor a H ha hH
  have hPow := mixed_spectator_power_le (show 0 ≤ 2*R by positivity) N
  have hConst := mixed_constant_le_exponential A hN
  calc
    _ ≤ (N:ℝ)^2*(C*(((N:ℝ)*simpleKernelConstant*((1+|Real.log c|)*(H+1)))*
        ((N:ℝ)*simpleKernelConstant*((1+|Real.log a|)*(H+1)))*(max 1 (2*R))^N)) := by
      unfold compactDiameterIntegralBudget
      gcongr
    _ = A*((N:ℝ)^4*(max 1 (2*R))^N*(H+1)^2) := by dsimp [A]; ring
    _ ≤ (max 1 A)^N*((N:ℝ)^4*(max 1 (2*R))^N*(H+1)^2) :=
      mul_le_mul_of_nonneg_right hConst (by positivity)
    _ = _ := by dsimp [K]; rw [mul_pow]; ring

/-- Both logarithmic pole costs, the finite pair cover, and the spectator
volume fit one dimension-exponential envelope. The threshold precedes N
and every lambda in the source small-current interval. -/
theorem actual_compact_right_radial_kernel_integral (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x ≤ 1) {δ c a : ℝ} (hδ : 0 < δ)
    (hδsmall : δ < 2*(1-Real.cos d.thetaB)) (hc : 0 < c) (ha : 0 < a)
    {D β : ℝ} (hD : 0 ≤ D) (hβ : 0 < β) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 0 < N → (N:ℝ) ≤ D*Real.sqrt H →
      ∀ τ lam : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ Real.exp (-β*H) →
      let G := currentUnwrappedPhase (N := N) f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
        (radialParameter d.theta (Real.exp (-H)))
      let S := Icc (fun _ : Fin N => -rightSectorRadius d.thetaB δ)
        (fun _ => rightSectorRadius d.thetaB δ)
      let L := fun x => twoPhaseKernel (c*Real.exp (-H)) (a*Real.exp (-H)) ((∑ i, x i),G x)
      IntegrableOn (fun x => allBranchExteriorDiameter x*L x) S ∧
      (∫ x in S, allBranchExteriorDiameter x*L x) ≤ K^N*(N:ℝ)^4*(H+1)^2 := by
  obtain ⟨C,hC,hbound⟩ := actual_compact_right_diameter_integral d hcsmall f hf hp1 hδ hδsmall hD hβ
  obtain ⟨hR,_⟩ := right_sector_radius_bounds d.thetaB_pos d.thetaB_lt hδ hδsmall
  obtain ⟨K,hK,hBudget⟩ := compact_diameter_kernel_radial_budget hC.le hR.le hc ha
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (0:ℝ),
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (inv_pos.mpr hc)),
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (inv_pos.mpr ha))]
    with H hboundH hH hec hea
  intro N hN hND τ lam hτ hτ1 hlam hlamB
  have hc1 : c*Real.exp (-H) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hec.le hc.le
    simpa only [mul_inv_cancel₀ hc.ne'] using hh
  have ha1 : a*Real.exp (-H) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hea.le ha.le
    simpa only [mul_inv_cancel₀ ha.ne'] using hh
  have hh := hboundH N hN hND τ lam hτ hτ1 hlam hlamB (c*Real.exp (-H)) (a*Real.exp (-H))
    (by positivity) hc1 (by positivity) ha1
  exact ⟨hh.1,hh.2.trans (hBudget N H hN hH)⟩

end
end IsingBulk.Tail
