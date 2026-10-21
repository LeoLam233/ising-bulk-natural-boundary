import IsingBulk.HT.Tail.SignedCompactCoarea
import IsingBulk.Tail.CompactKernelRadialBudget

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Lie Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 1800000

theorem shiftedCoordinatePhaseKernel_update (ξ ζ : ℝ) {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    (F G : (Fin N → ℝ) → ℝ) (a b : ℝ) (x : Fin N → ℝ) :
    shiftedCoordinatePhaseKernel i j a b ξ ζ (twoPhaseUpdate F G i j x)=
      shiftedTwoPhaseKernel a b ξ ζ (F x,G x) := by
  simp [shiftedCoordinatePhaseKernel,twoPhaseUpdate,shiftedTwoPhaseKernel,shiftedPhaseKernel,Ne.symm hij]

/-- Actual compact-right phase kernel on the entire signed cube, with all
spectator volume and all periods retained. -/
theorem signed_actual_compact_right_diameter_integral (ξ ζ : ℝ) (d : IsingBulk.Branch.LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x ≤ 1) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 2*(1-Real.cos d.thetaB))
    {D β : ℝ} (hD : 0 ≤ D) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 0 < N → (N:ℝ) ≤ D*Real.sqrt H →
      ∀ τ lam : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ lam → lam ≤ Real.exp (-β*H) →
      ∀ a b : ℝ, 0 < a → a ≤ 1 → 0 < b → b ≤ 1 →
      let G := currentUnwrappedPhase (N := N) f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
        (radialParameter d.theta (Real.exp (-H)))
      let S := Icc (fun _ : Fin N => -rightSectorRadius d.thetaB δ)
        (fun _ => rightSectorRadius d.thetaB δ)
      let K := fun x => shiftedTwoPhaseKernel a b ξ ζ ((∑ i, x i),G x)
      IntegrableOn (fun x => allBranchExteriorDiameter x*K x) S ∧
      (∫ x in S, allBranchExteriorDiameter x*K x) ≤
        (N:ℝ)^2*(C*(((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*(2*rightSectorRadius d.thetaB δ)^(N-2))) := by
  obtain ⟨C,hC,hpairs⟩ := signed_actual_compact_right_pair_coarea ξ ζ d hcsmall f hf hp1 hδ hδsmall hD hβ
  obtain ⟨hR,_⟩ := right_sector_radius_bounds d.thetaB_pos d.thetaB_lt hδ hδsmall
  refine ⟨C,hC,?_⟩
  filter_upwards [hpairs,radial_current_phase_eventually_smooth d hcsmall f hf] with H hpair hphase
  intro N hN hND τ lam hτ hτ1 hlam hlamB a b ha ha1 hb hb1
  dsimp only
  apply compact_diameter_integral_of_pair_bounds
  · exact (shiftedTwoPhaseKernel_continuous ha hb ξ ζ).comp
      ((continuous_finsetSum _ (fun i _ => continuous_apply i)).prodMk
        (hphase N hN τ lam hτ hlam).continuous)
  · intro x; exact shiftedTwoPhaseKernel_nonneg _ _ _ _ _
  · have := simpleKernelConstant_pos
    positivity
  · intro i j hij
    simpa only [shiftedCoordinatePhaseKernel_update ξ ζ hij] using
      hpair N hN hND τ lam i j hij hτ hτ1 hlam hlamB a b ha ha1 hb hb1


theorem signed_actual_compact_right_radial_kernel_integral (ξ ζ : ℝ) (d : LocalBranchData)
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
      let L := fun x => shiftedTwoPhaseKernel (c*Real.exp (-H)) (a*Real.exp (-H)) ξ ζ ((∑ i, x i),G x)
      IntegrableOn (fun x => allBranchExteriorDiameter x*L x) S ∧
      (∫ x in S, allBranchExteriorDiameter x*L x) ≤ K^N*(N:ℝ)^4*(H+1)^2 := by
  obtain ⟨C,hC,hbound⟩ := signed_actual_compact_right_diameter_integral ξ ζ d hcsmall f hf hp1 hδ hδsmall hD hβ
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
end IsingBulk.HT.Tail
