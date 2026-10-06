import IsingBulk.Tail.MixedAnalyticDensityModel

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The density recurrence is an equality of joint germs, with the source
cutoff plateaus and both global kernels proved inside the same neighborhood. -/
theorem mixed_analytic_density_lie_germ {n : ℕ}
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
    (C : ℂ) (F : MixedActiveSpace (n+1) → ℂ) (hF : AnalyticAt ℂ F 0) :
    let φ := fun i => mixedContourPhase f r τ lam s background i
    let y := deformedPoint f r τ lam background
    Function.uncurry (IsingBulk.Lie.lieStep
      (fun z a => mixedContourVelocity J j q f r τ lam z (mixedFreeze (insert q J) background a))
      (mixedAnalyticDensityModel J q f r τ lam s background C F)) =ᶠ[𝓝 (s,background)]
    Function.uncurry (mixedAnalyticDensityModel J q f r τ lam s background C
      (mixedRegularDensityStep (mixedActiveParameterDirection (n+1)) (mixedActiveBranchDirection j)
        (mixedActiveCompactDirection (n+1)) (mixedActiveBranchResidual J j q s φ y)
        (mixedActiveCompactResidual J j q s φ y) F)) := by
  have hd := mixedHybridDivergence_active_germ (Nat.succ_pos n) J j q hj hq f hr τ lam s background
    hp_smooth hm_smooth hΩ hbranch hp hm hR₁ hR₂
  have hdisp : Tendsto (fun p : ℂ × (Fin (n+1) → ℝ) =>
      mixedSourceDisplacement J q f r τ lam s background p.1 p.2) (𝓝 (s,background)) (𝓝 0) := by
    have hh := (mixedSourceDisplacement_contDiffAt J j q f hr τ lam s background s background hp_smooth hm_smooth
      (by simpa only [mixedFreeze_self] using hΩ)).continuousAt.tendsto
    simpa only [mixedSourceDisplacement_zero] using hh
  dsimp only at hd ⊢
  filter_upwards [mixed_active_source_neighborhood J j q f hr τ lam s background hp_smooth hm_smooth hΩ hbranch hp hm,
    hd,hdisp.eventually hF.eventually_analyticAt] with p hdata hdiv hFp
  apply mixed_density_kernel_attach J j q hj f hr τ lam s background p.1 p.2 hp_smooth hm_smooth
    (fun i hi => (hdata.2.2 i hi).2.2) hdata.1 C F _ hFp.differentiableAt
  exact mixed_frozen_regular_lie J j q hj hq f hr τ lam s background p.1 p.2 hp_smooth hm_smooth
    (fun i hi => (hdata.2.2 i hi).1) (fun i hi => (hdata.2.2 i hi).2.1)
    (fun i hi => (hdata.2.2 i hi).2.2) hdata.2.1 hdata.1 F hFp.differentiableAt hdiv

theorem lieStep_congr_joint_germ {n : ℕ}
    (V : ℂ → (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    {A B : ℂ → (Fin (n+1) → ℝ) → ℂ} (s : ℂ) (x : Fin (n+1) → ℝ)
    (h : Function.uncurry A =ᶠ[𝓝 (s,x)] Function.uncurry B) :
    IsingBulk.Lie.lieStep V A s x=IsingBulk.Lie.lieStep V B s x := by
  have hp : (fun t => A t x) =ᶠ[𝓝 s] (fun t => B t x) :=
    h.comp_tendsto (continuousAt_id.prodMk continuousAt_const).tendsto
  have hx : (A s) =ᶠ[𝓝 x] (B s) :=
    h.comp_tendsto (continuousAt_const.prodMk continuousAt_id).tendsto
  have hf (i : Fin (n+1)) : (fun z => V s z i*A s z)=ᶠ[𝓝 x] (fun z => V s z i*B s z) := by
    filter_upwards [hx] with z hz
    rw [hz]
  simp only [IsingBulk.Lie.lieStep,IsingBulk.Lie.divergence,hp.deriv_eq,(hf _).fderiv_eq]

theorem lieStep_joint_germ {n : ℕ}
    (V : ℂ → (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    {A B : ℂ → (Fin (n+1) → ℝ) → ℂ} (s : ℂ) (x : Fin (n+1) → ℝ)
    (h : Function.uncurry A =ᶠ[𝓝 (s,x)] Function.uncurry B) :
    Function.uncurry (IsingBulk.Lie.lieStep V A)=ᶠ[𝓝 (s,x)] Function.uncurry (IsingBulk.Lie.lieStep V B) := by
  filter_upwards [h.eventuallyEq_nhds] with p hp
  exact lieStep_congr_joint_germ V p.1 p.2 hp

end
end IsingBulk.Tail
