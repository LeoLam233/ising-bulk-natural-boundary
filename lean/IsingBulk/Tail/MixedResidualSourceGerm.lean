import IsingBulk.Tail.MixedFrozenScalarTransport

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem mixed_residuals_frozen_source {N : ℕ} (hN : 0<N)
    (J : Finset (Fin N)) (j q : Fin N) (hj : j∈J) (hq : q∉J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (s : ℂ) (background : Fin N → ℝ) (t : ℂ) (x : Fin N → ℝ)
    (hp : ∀ i∈insert q J,f.p (x i)=f.p (background i))
    (hm : ∀ i∈insert q J,f.m (x i)=f.m (background i))
    (hbranch : ∀ i∈J,Real.sin (mixedFreeze (insert q J) background x i)<0)
    (hΩ : (t,mixedFreeze (insert q J) background x)∈mixedSeparatedDomain J j q f r τ lam) :
    let θ := mixedFreeze (insert q J) background x
    let u := mixedSourceDisplacement J q f r τ lam s background t x
    let φ := fun i => mixedContourPhase f r τ lam s background i
    let y := deformedPoint f r τ lam background
    (∀ i∈J,mixedBranchResidual J j q f r τ lam t θ i=
      if i=j then mixedActiveBranchResidual J j q s φ y u else 0) ∧
    mixedContourVelocity J j q f r τ lam t θ q= -mixedActiveCompactResidual J j q s φ y u := by
  let θ := mixedFreeze (insert q J) background x
  have hb : mixedSourceSlope t (deformedPoint f r τ lam θ j)≠0 := by
    unfold mixedSourceSlope
    exact div_ne_zero (mul_ne_zero Complex.I_ne_zero (hΩ.2.2.1 j hj))
      (mul_ne_zero (by norm_num) (mixedSourcePhase_sin_ne (hΩ.2.1 j)))
  obtain ⟨hR,hQ⟩ := mixed_active_residuals_frozen_model J j q hj hq f r τ lam s background t x hp hm
  dsimp only
  constructor
  · intro i hi
    by_cases hij : i=j
    · subst i
      simp only [ite_true]
      rw [hR]
      exact mixedBranchResidual_zero_source hN J j q f hr τ lam t θ hj hq hbranch hΩ.2.1
        (hΩ.2.2.1 j hj) hb hΩ.2.2.2.1
    · simp only [hij,ite_false,mixedBranchResidual,mixedContourVelocity]
      rw [mixedVelocity_other_branch _ _ _ _ _ hi hij hq,
        mixedSourceSlope_mul_A (hΩ.2.2.1 i hi),sub_self]
  · rw [hQ,mixedCompactVelocity_zero_source hN J j q f hr τ lam t θ hj hq hbranch hΩ.2.1 hb hΩ.2.2.2.1]
    simp [mixedActiveCompactResidual,mixedContourPhase,θ]

/-- Both residual identities hold on one joint source neighborhood, with
the active analytic models fixed at the original background. -/
theorem mixed_residuals_active_germ {N : ℕ} (hN : 0<N)
    (J : Finset (Fin N)) (j q : Fin N) (hj : j∈J) (hq : q∉J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ)
    (background : Fin N → ℝ) (hp_smooth : ContDiff ℝ ∞ f.p) (hm_smooth : ContDiff ℝ ∞ f.m)
    (hΩ : (s,background)∈mixedSeparatedDomain J j q f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (background i)<0)
    (hp : ∀ i∈insert q J,f.p =ᶠ[𝓝 (background i)] (fun _ => f.p (background i)))
    (hm : ∀ i∈insert q J,f.m =ᶠ[𝓝 (background i)] (fun _ => f.m (background i))) :
    let φ := fun i => mixedContourPhase f r τ lam s background i
    let y := deformedPoint f r τ lam background
    ∀ᶠ p : ℂ × (Fin N → ℝ) in 𝓝 (s,background),
      (∀ i∈J,mixedBranchResidual J j q f r τ lam p.1 (mixedFreeze (insert q J) background p.2) i=
        if i=j then mixedActiveBranchResidual J j q s φ y
          (mixedSourceDisplacement J q f r τ lam s background p.1 p.2) else 0) ∧
      mixedContourVelocity J j q f r τ lam p.1 (mixedFreeze (insert q J) background p.2) q=
        -mixedActiveCompactResidual J j q s φ y
          (mixedSourceDisplacement J q f r τ lam s background p.1 p.2) := by
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
  exact mixed_residuals_frozen_source hN J j q hj hq f hr τ lam s background p.1 p.2
    (fun i hi => (hpp i hi).1) (fun i hi => (hpm i hi).1) hpb hpΩ

end
end IsingBulk.Tail
