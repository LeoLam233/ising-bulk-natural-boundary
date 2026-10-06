import IsingBulk.Tail.CompactPairCoordinates

/-! The actual coupled compact-right two-row source Jacobian. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem radial_current_phase_eventually_smooth (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f) :
    ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 0<N → ∀ τ lam : ℝ, 0≤τ → 0≤lam →
      ContDiff ℝ ∞ (currentUnwrappedPhase (N := N) f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
        (radialParameter d.theta (Real.exp (-H)))) := by
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨e,he,_,hmarginS⟩ := radialDampingMargin_linear hsint hcsmall
  filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds he)] with H hepsE
  intro N hN τ lam hτ hlam
  let eps := Real.exp (-H)
  let r := Real.exp (-d.c₀*eps)
  let s := radialParameter d.theta eps
  have heps : 0<eps := Real.exp_pos _
  have hr : 0<r := Real.exp_pos _
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hmarg : r⁻¹-r<(sourceS s).im := by
    have hh := radialRadius_parameter_margin heps (hmarginS eps heps hepsE)
    change r⁻¹-r+Real.sin d.theta*eps<_ at hh
    linarith [mul_pos hsint heps]
  exact currentUnwrappedPhase_contDiff hN f hr hr1 hτ hlam hf.p_smooth hf.m_smooth
    hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero hmarg

/-- One threshold before N, epsilon, and lambda. The determinant is that of
the literal N-coordinate map with two phase rows and unchanged spectators. -/
theorem actual_compact_right_pair_jacobian (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (f : SelectorFunctions) (hf : RegularSelector f)
    (hp1 : ∀ x, f.p x≤1) {δ : ℝ} (hδ : 0<δ) (hδsmall : δ<2*(1-Real.cos d.thetaB))
    {D β : ℝ} (hD : 0≤D) (hβ : 0<β) :
    ∃ k : ℝ, 0<k ∧ ∀ᶠ H : ℝ in atTop, ∀ (N : ℕ), 0<N → (N:ℝ)≤D*Real.sqrt H →
      ∀ (τ lam : ℝ) (x : Fin N → ℝ) (i j : Fin N), i≠j → x i≤x j →
      0≤τ → τ≤1 → 0≤lam → lam≤Real.exp (-β*H) →
      (∀ l, x l∈Icc (-rightSectorRadius d.thetaB δ) (rightSectorRadius d.thetaB δ)) →
      let G := currentUnwrappedPhase (N := N) f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
        (radialParameter d.theta (Real.exp (-H)))
      HasFDerivAt (twoPhaseUpdate (fun y => ∑ l, y l) G i j)
        (twoPhaseUpdateDeriv (coordinateSumLinear N) (fderiv ℝ G x) i j) x ∧
      k*(x j-x i)≤fderiv ℝ G x (pairDirection i j) ∧
      k*(x j-x i)≤|(twoPhaseUpdateDeriv (coordinateSumLinear N) (fderiv ℝ G x) i j).det| := by
  obtain ⟨k,hk,hslope⟩ := actual_compact_right_pair_slope d hcsmall f hf hp1 hδ hδsmall hD hβ
  refine ⟨k/2,half_pos hk,?_⟩
  filter_upwards [hslope,radial_current_phase_eventually_smooth d hcsmall f hf] with H hpair hsmooth
  intro N hN hND τ lam x i j hij horder hτ hτ1 hlam hlamB hx
  let G := currentUnwrappedPhase (N := N) f (Real.exp (-d.c₀*Real.exp (-H))) τ lam
    (radialParameter d.theta (Real.exp (-H)))
  have hG : ContDiff ℝ ∞ G := hsmooth N hN τ lam hτ hlam
  have hGd := hG.differentiable (by simp) x
  have hh := hpair N hN hND τ lam (pairMidpoint x i j) i j ((x i-x j)/2) hij
    (pairMidpoint_equal x hij) (by linarith) hτ hτ1 hlam hlamB
    (fun t ht => pairMidpoint_path_mem x hij horder hx ht)
  change k*(-((x i-x j)/2))≤deriv (fun u => G (pairMidpoint x i j+u • pairDirection i j)) ((x i-x j)/2) at hh
  rw [pair_curve_deriv_at_recovery hGd] at hh
  have hs : (k/2)*(x j-x i)≤fderiv ℝ G x (pairDirection i j) := by linarith
  refine ⟨?_,hs,?_⟩
  · apply twoPhaseUpdate_hasFDerivAt _ hGd.hasFDerivAt
    convert (coordinateSumLinear N).hasFDerivAt (x := x) using 1
    ext y
    exact (coordinateSumLinear_apply y).symm
  · rw [sumPhaseUpdate_det _ hij,abs_neg]
    exact hs.trans (le_abs_self _)

end
end IsingBulk.Tail
