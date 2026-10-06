import IsingBulk.Tail.MixedCutoffTerm

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem MixedDensityJetTerm.source_step_germ {n : ℕ}
    (T : MixedDensityJetTerm (n+1) (MixedActiveSpace (n+1)))
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (hj : j∈J) (hq : q∉J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ)
    (background : Fin (n+1) → ℝ) (hp_smooth : ContDiff ℝ ∞ f.p) (hm_smooth : ContDiff ℝ ∞ f.m)
    (hΩ : (s,background)∈mixedSeparatedDomain J j q f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (background i)<0)
    (hp : ∀ i∈insert q J,f.p =ᶠ[𝓝 (background i)] (fun _ => f.p (background i)))
    (hm : ∀ i∈insert q J,f.m =ᶠ[𝓝 (background i)] (fun _ => f.m (background i)))
    (hR₁ : AnalyticAt ℂ (mixedActiveBranchResidual J j q s
      (fun i => mixedContourPhase f r τ lam s background i) (deformedPoint f r τ lam background)) 0)
    (hR₂ : AnalyticAt ℂ (mixedActiveCompactResidual J j q s
      (fun i => mixedContourPhase f r τ lam s background i) (deformedPoint f r τ lam background)) 0)
    (C : ℂ) (w : (Fin (n+1) → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hT : AnalyticAt ℂ T.regularPart 0) :
    let φ := fun i => mixedContourPhase f r τ lam s background i
    let y := deformedPoint f r τ lam background
    Function.uncurry (IsingBulk.Lie.lieStep
      (fun z a => mixedContourVelocity J j q f r τ lam z (mixedFreeze (insert q J) background a))
      (T.sourceValue J q f r τ lam s background C w)) =ᶠ[𝓝 (s,background)] (fun p =>
      ((mixedDensityActions (n+1)).map (fun a =>
        (T.child (mixedActiveParameterDirection (n+1)) (mixedActiveBranchDirection j)
          (mixedActiveCompactDirection (n+1)) (mixedActiveBranchResidual J j q s φ y)
          (mixedActiveCompactResidual J j q s φ y) (mixedActiveAngularVelocity J j q s φ y) a).sourceValue
          J q f r τ lam s background C w p.1 p.2)).sum) := by
  have hg := mixed_analytic_density_lie_germ J j q hj hq f hr τ lam s background hp_smooth hm_smooth
    hΩ hbranch hp hm hR₁ hR₂ C T.regularPart hT
  have hdisp : Tendsto (fun p : ℂ × (Fin (n+1) → ℝ) =>
      mixedSourceDisplacement J q f r τ lam s background p.1 p.2) (𝓝 (s,background)) (𝓝 0) := by
    have hh := (mixedSourceDisplacement_contDiffAt J j q f hr τ lam s background s background hp_smooth hm_smooth
      (by simpa only [mixedFreeze_self] using hΩ)).continuousAt.tendsto
    simpa only [mixedSourceDisplacement_zero] using hh
  dsimp only at hg ⊢
  filter_upwards [mixed_active_source_neighborhood J j q f hr τ lam s background hp_smooth hm_smooth hΩ hbranch hp hm,
    hg,hdisp.eventually hT.eventually_analyticAt] with p hdata hstep hTp
  apply T.source_step J j q hj f hr τ lam s background C w hw p.1 p.2 hp_smooth hm_smooth hdata.1
    hTp.differentiableAt _ _ _ _ hstep
  intro i
  exact mixed_velocity_frozen_model (Nat.succ_pos n) J j q i hj hq f hr τ lam s background p.1 p.2
    (fun k hk => (hdata.2.2 k hk).1) (fun k hk => (hdata.2.2 k hk).2.1) hdata.2.1 hdata.1

end
end IsingBulk.Tail
