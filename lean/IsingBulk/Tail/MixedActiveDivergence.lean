import IsingBulk.Tail.MixedResidualSourceGerm

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

theorem mixedDisplacementAngularColumn_branch {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (hj : j∈J) (hq : q∉J) (b : Fin N → ℂ) :
    mixedDisplacementAngularColumn J q j b=b j • mixedActiveBranchDirection j := by
  have hqj : q≠j := by intro h; subst q; exact hq hj
  apply Prod.ext
  · simp [mixedDisplacementAngularColumn,mixedActiveBranchDirection]
  · apply Prod.ext
    · ext i
      by_cases hij : i=j
      · subst i; simp [mixedDisplacementAngularColumn,mixedActiveBranchDirection,hj]
      · simp [mixedDisplacementAngularColumn,mixedActiveBranchDirection,hij]
    · simp [mixedDisplacementAngularColumn,mixedActiveBranchDirection,hqj]

theorem mixedDisplacementAngularColumn_compact {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (hq : q∉J) (b : Fin N → ℂ) :
    mixedDisplacementAngularColumn J q q b=mixedActiveCompactDirection N := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · ext i
      by_cases hi : i=q
      · subst i; simp [mixedDisplacementAngularColumn,mixedActiveCompactDirection,hq]
      · simp [mixedDisplacementAngularColumn,mixedActiveCompactDirection,hi]
    · simp [mixedDisplacementAngularColumn,mixedActiveCompactDirection]

theorem coordDeriv_eq_of_germ {N : ℕ} (x : Fin N → ℝ) (i : Fin N)
    {F G : (Fin N → ℝ) → ℂ} (h : F =ᶠ[𝓝 x] G) : coordDeriv F x i=coordDeriv G x i := by
  have ht : Tendsto (fun u => Function.update x i u) (𝓝 (x i)) (𝓝 x) := by
    simpa only [Function.update_eq_self] using (hasDerivAt_update x i (x i)).continuousAt.tendsto
  exact (h.comp_tendsto ht).deriv_eq

theorem mixed_frozen_active_coordDeriv {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (s : ℂ) (background : Fin N → ℝ) (t : ℂ) (x : Fin N → ℝ) (k : Fin N)
    (hp : ∀ i,DifferentiableAt ℝ f.p (mixedFreeze (insert q J) background x i))
    (hm : ∀ i,DifferentiableAt ℝ f.m (mixedFreeze (insert q J) background x i))
    (hplateau : ∀ i∈insert q J,deriv f.p (mixedFreeze (insert q J) background x i)=0 ∧
      deriv f.m (mixedFreeze (insert q J) background x i)=0)
    (hW : ∀ i∈J,0<(sourceW t (deformedPoint f r τ lam (mixedFreeze (insert q J) background x) i)).im)
    (F : MixedActiveSpace N → ℂ)
    (hF : DifferentiableAt ℂ F (mixedSourceDisplacement J q f r τ lam s background t x)) :
    coordDeriv (fun z => F (mixedSourceDisplacement J q f r τ lam s background t z)) x k=
      fderiv ℂ F (mixedSourceDisplacement J q f r τ lam s background t x)
        (mixedDisplacementAngularColumn J q k (fun i => mixedSourceSlope t
          (deformedPoint f r τ lam (mixedFreeze (insert q J) background x) i))) := by
  have hd := mixedSourceDisplacement_angular J q f hr τ lam s background t x k hp hm hplateau hW
  unfold coordDeriv
  simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars'] using
    ((hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (x k) hd
      (by simp only [Function.update_eq_self])).deriv

/-- A source residual germ determines the complete hybrid divergence. The
premises here are the identities proved by mixed_residuals_active_germ. -/
theorem mixedHybridDivergence_of_active_germ {N : ℕ}
    (J : Finset (Fin N)) (j q : Fin N) (hj : j∈J) (hq : q∉J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (s : ℂ) (background : Fin N → ℝ) (t : ℂ) (x : Fin N → ℝ)
    (hp : ∀ i,DifferentiableAt ℝ f.p (mixedFreeze (insert q J) background x i))
    (hm : ∀ i,DifferentiableAt ℝ f.m (mixedFreeze (insert q J) background x i))
    (hplateau : ∀ i∈insert q J,deriv f.p (mixedFreeze (insert q J) background x i)=0 ∧
      deriv f.m (mixedFreeze (insert q J) background x i)=0)
    (hW : ∀ i∈J,0<(sourceW t (deformedPoint f r τ lam (mixedFreeze (insert q J) background x) i)).im)
    (hb : mixedSourceSlope t (deformedPoint f r τ lam (mixedFreeze (insert q J) background x) j)≠0)
    (R₁ R₂ : MixedActiveSpace N → ℂ)
    (hR₁ : DifferentiableAt ℂ R₁ (mixedSourceDisplacement J q f r τ lam s background t x))
    (hR₂ : DifferentiableAt ℂ R₂ (mixedSourceDisplacement J q f r τ lam s background t x))
    (hR : ∀ i∈J,(fun z => mixedBranchResidual J j q f r τ lam t (mixedFreeze (insert q J) background z) i)
      =ᶠ[𝓝 x] (fun z => if i=j then R₁ (mixedSourceDisplacement J q f r τ lam s background t z) else 0))
    (hQ : (fun z => mixedContourVelocity J j q f r τ lam t (mixedFreeze (insert q J) background z) q)
      =ᶠ[𝓝 x] (fun z => -R₂ (mixedSourceDisplacement J q f r τ lam s background t z))) :
    let u := mixedSourceDisplacement J q f r τ lam s background t x
    mixedHybridDivergence J j q f r τ lam t (mixedFreeze (insert q J) background x)=
      fderiv ℂ R₁ u (mixedActiveBranchDirection j)+fderiv ℂ R₂ u (mixedActiveCompactDirection N) := by
  let θ := mixedFreeze (insert q J) background x
  let u := mixedSourceDisplacement J q f r τ lam s background t x
  have h₁ := mixed_frozen_active_coordDeriv J q f hr τ lam s background t x j hp hm hplateau hW R₁ hR₁
  rw [mixedDisplacementAngularColumn_branch J j q hj hq,map_smul,smul_eq_mul] at h₁
  have h₂ := mixed_frozen_active_coordDeriv J q f hr τ lam s background t x q hp hm hplateau hW R₂ hR₂
  rw [mixedDisplacementAngularColumn_compact J q hq] at h₂
  have hterm (i : Fin N) (hi : i∈J) :
      coordDeriv (fun z => mixedBranchResidual J j q f r τ lam t z i) θ i/
        mixedSourceSlope t (deformedPoint f r τ lam θ i)=
      if i=j then fderiv ℂ R₁ u (mixedActiveBranchDirection j) else 0 := by
    have hf := coordDeriv_mixedFreeze (insert q J) background x
      (fun z => mixedBranchResidual J j q f r τ lam t z i) i
    rw [ite_eq_left (Finset.mem_insert_of_mem hi)] at hf
    rw [← hf,coordDeriv_eq_of_germ x i (hR i hi)]
    by_cases hij : i=j
    · subst i
      simp only [ite_true]
      rw [h₁]
      exact mul_div_cancel_left₀ _ hb
    · simp [hij,coordDeriv]
  have hqterm : coordDeriv (fun z => mixedContourVelocity J j q f r τ lam t z q) θ q=
      -fderiv ℂ R₂ u (mixedActiveCompactDirection N) := by
    have hf := coordDeriv_mixedFreeze (insert q J) background x
      (fun z => mixedContourVelocity J j q f r τ lam t z q) q
    rw [ite_eq_left (Finset.mem_insert_self q J)] at hf
    rw [← hf,coordDeriv_eq_of_germ x q hQ]
    change deriv (-(fun a => R₂ (mixedSourceDisplacement J q f r τ lam s background t (Function.update x q a)))) (x q)=_
    rw [deriv.neg]
    exact congrArg Neg.neg h₂
  have hcterm (i : Fin N) (hi : i∈Finset.univ.filter (fun i => i∉J)) :
      coordDeriv (fun z => mixedContourVelocity J j q f r τ lam t z i) θ i=
      if i=q then -fderiv ℂ R₂ u (mixedActiveCompactDirection N) else 0 := by
    by_cases hiq : i=q
    · subst i; simpa only [ite_true] using hqterm
    · simp only [hiq,ite_false]
      have he : (fun z => mixedContourVelocity J j q f r τ lam t z i)=fun _ => (0:ℂ) := by
        funext z
        exact mixedContourVelocity_zero J j q i f r τ lam t z hj (Finset.mem_filter.mp hi).2 hiq
      rw [he,coordDeriv]
      simp
  change (∑ i∈J,_)-(∑ i∈Finset.univ.filter (fun i => i∉J),_)=_
  rw [Finset.sum_congr rfl hterm,Finset.sum_congr rfl hcterm]
  simp [hj,hq,u]

end
end IsingBulk.Tail
