import IsingBulk.Tail.MixedActiveChartSmooth

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem mixed_active_source_neighborhood {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ)
    (background : Fin N → ℝ) (hp_smooth : ContDiff ℝ ∞ f.p) (hm_smooth : ContDiff ℝ ∞ f.m)
    (hΩ : (s,background)∈mixedSeparatedDomain J j q f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (background i)<0)
    (hp : ∀ i∈insert q J,f.p =ᶠ[𝓝 (background i)] (fun _ => f.p (background i)))
    (hm : ∀ i∈insert q J,f.m =ᶠ[𝓝 (background i)] (fun _ => f.m (background i))) :
    ∀ᶠ p : ℂ × (Fin N → ℝ) in 𝓝 (s,background),
      (p.1,mixedFreeze (insert q J) background p.2)∈mixedSeparatedDomain J j q f r τ lam ∧
      (∀ i∈J,Real.sin (mixedFreeze (insert q J) background p.2 i)<0) ∧
      ∀ i∈insert q J,f.p (p.2 i)=f.p (background i) ∧ f.m (p.2 i)=f.m (background i) ∧
        deriv f.p (mixedFreeze (insert q J) background p.2 i)=0 ∧
        deriv f.m (mixedFreeze (insert q J) background p.2 i)=0 := by
  let H := fun p : ℂ × (Fin N → ℝ) => (p.1,mixedFreeze (insert q J) background p.2)
  have hH : Continuous H := continuous_fst.prodMk ((mixedFreeze_continuous _ _).comp continuous_snd)
  have hΩnear : ∀ᶠ p in 𝓝 (s,background),H p∈mixedSeparatedDomain J j q f r τ lam := by
    apply hH.continuousAt.eventually
    apply (mixedSeparatedDomain_isOpen J j q f hr τ lam hp_smooth hm_smooth).mem_nhds
    simpa only [H,mixedFreeze_self] using hΩ
  have hbnear : ∀ᶠ x in 𝓝 background,∀ i∈J,Real.sin (mixedFreeze (insert q J) background x i)<0 := by
    apply (Filter.eventually_all_finset J).mpr
    intro i hi
    have hc : Continuous (fun x => Real.sin (mixedFreeze (insert q J) background x i)) :=
      Real.continuous_sin.comp ((continuous_apply i).comp (mixedFreeze_continuous _ _))
    exact (hc.continuousAt (x := background)).eventually_lt continuousAt_const
      (by simpa only [mixedFreeze_self] using hbranch i hi)
  have hsnd : Tendsto (fun p : ℂ × (Fin N → ℝ) => p.2) (𝓝 (s,background)) (𝓝 background) :=
    continuous_snd.continuousAt.tendsto
  filter_upwards [hΩnear,hsnd.eventually (mixed_plateau_data_eventually (insert q J) background f.p hp),
    hsnd.eventually (mixed_plateau_data_eventually (insert q J) background f.m hm),hsnd.eventually hbnear]
    with p hpΩ hpp hpm hpb
  refine ⟨hpΩ,hpb,?_⟩
  intro i hi
  refine ⟨(hpp i hi).1,(hpm i hi).1,?_,?_⟩
  · simpa only [mixedFreeze,hi,ite_true,(hpp i hi).2,deriv_const] using (hp i hi).deriv_eq
  · simpa only [mixedFreeze,hi,ite_true,(hpm i hi).2,deriv_const] using (hm i hi).deriv_eq

/-- The actual hybrid divergence matches fixed-background analytic residual
derivatives on a neighborhood, as required for repeated Lie differentiation. -/
theorem mixedHybridDivergence_active_germ {N : ℕ} (hN : 0<N)
    (J : Finset (Fin N)) (j q : Fin N) (hj : j∈J) (hq : q∉J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ)
    (background : Fin N → ℝ) (hp_smooth : ContDiff ℝ ∞ f.p) (hm_smooth : ContDiff ℝ ∞ f.m)
    (hΩ : (s,background)∈mixedSeparatedDomain J j q f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (background i)<0)
    (hp : ∀ i∈insert q J,f.p =ᶠ[𝓝 (background i)] (fun _ => f.p (background i)))
    (hm : ∀ i∈insert q J,f.m =ᶠ[𝓝 (background i)] (fun _ => f.m (background i)))
    (hR₁ : AnalyticAt ℂ (mixedActiveBranchResidual J j q s
      (fun i => mixedContourPhase f r τ lam s background i) (deformedPoint f r τ lam background)) 0)
    (hR₂ : AnalyticAt ℂ (mixedActiveCompactResidual J j q s
      (fun i => mixedContourPhase f r τ lam s background i) (deformedPoint f r τ lam background)) 0) :
    let φ := fun i => mixedContourPhase f r τ lam s background i
    let y := deformedPoint f r τ lam background
    (fun p : ℂ × (Fin N → ℝ) => mixedHybridDivergence J j q f r τ lam p.1
      (mixedFreeze (insert q J) background p.2)) =ᶠ[𝓝 (s,background)] (fun p =>
      fderiv ℂ (mixedActiveBranchResidual J j q s φ y)
        (mixedSourceDisplacement J q f r τ lam s background p.1 p.2) (mixedActiveBranchDirection j)+
      fderiv ℂ (mixedActiveCompactResidual J j q s φ y)
        (mixedSourceDisplacement J q f r τ lam s background p.1 p.2) (mixedActiveCompactDirection N)) := by
  have hg := mixed_residuals_active_germ hN J j q hj hq f hr τ lam s background hp_smooth hm_smooth hΩ hbranch hp hm
  dsimp only at hg ⊢
  have hdisp : Tendsto (fun p : ℂ × (Fin N → ℝ) =>
      mixedSourceDisplacement J q f r τ lam s background p.1 p.2) (𝓝 (s,background)) (𝓝 0) := by
    have hh := (mixedSourceDisplacement_contDiffAt J j q f hr τ lam s background s background hp_smooth hm_smooth
      (by simpa only [mixedFreeze_self] using hΩ)).continuousAt.tendsto
    simpa only [mixedSourceDisplacement_zero] using hh
  filter_upwards [mixed_active_source_neighborhood J j q f hr τ lam s background hp_smooth hm_smooth hΩ hbranch hp hm,
    hg.eventually_nhds,hdisp.eventually hR₁.eventually_analyticAt,hdisp.eventually hR₂.eventually_analyticAt]
    with p hdata hpg hpa hpb
  have hslice := (continuousAt_const.prodMk (continuousAt_id (x := p.2))).tendsto.eventually hpg
  have hb : mixedSourceSlope p.1 (deformedPoint f r τ lam (mixedFreeze (insert q J) background p.2) j)≠0 := by
    unfold mixedSourceSlope
    exact div_ne_zero (mul_ne_zero Complex.I_ne_zero (hdata.1.2.2.1 j hj))
      (mul_ne_zero (by norm_num) (mixedSourcePhase_sin_ne (hdata.1.2.1 j)))
  apply mixedHybridDivergence_of_active_germ J j q hj hq f hr τ lam s background p.1 p.2
    (fun _ => hp_smooth.differentiable (by simp) _) (fun _ => hm_smooth.differentiable (by simp) _)
    (fun i hi => (hdata.2.2 i hi).2.2) (fun i _ => hdata.1.2.1 i) hb _ _ hpa.differentiableAt hpb.differentiableAt
  · intro i hi
    filter_upwards [hslice] with z hz
    exact hz.1 i hi
  · filter_upwards [hslice] with z hz
    exact hz.2

end
end IsingBulk.Tail
