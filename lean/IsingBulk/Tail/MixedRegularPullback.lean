import IsingBulk.Tail.MixedSourceNeighborhood
import IsingBulk.Tail.MixedFreezeCalculus
import IsingBulk.Tail.MixedSeparatedVelocity

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def mixedRegularPullback {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (background : Fin N → ℝ)
    (F : MixedActiveSpace N → ℂ) (t : ℂ) (x : Fin N → ℝ) : ℂ :=
  mixedHybridVolume J f r τ lam t (mixedFreeze (insert q J) background x)*
    F (mixedSourceDisplacement J q f r τ lam s background t x)

theorem mixedRegularPullback_differentiable {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (s : ℂ) (background : Fin N → ℝ) (t : ℂ) (x : Fin N → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hΩ : (t,mixedFreeze (insert q J) background x)∈mixedSeparatedDomain J j q f r τ lam)
    (F : MixedActiveSpace N → ℂ)
    (hF : DifferentiableAt ℂ F (mixedSourceDisplacement J q f r τ lam s background t x)) :
    DifferentiableAt ℂ (fun z => mixedRegularPullback J q f r τ lam s background F z x) t ∧
    DifferentiableAt ℝ (mixedRegularPullback J q f r τ lam s background F t) x := by
  have hAs := (hF.hasFDerivAt.comp_hasDerivAt t
    (mixedSourceDisplacement_parameter J q f r τ lam s background t x hΩ.1 (fun i _ => hΩ.2.1 i))).differentiableAt
  have hEs := (mixedHybridVolume_parameter J f r τ lam t (mixedFreeze (insert q J) background x)
    hΩ.1 (fun i _ => hΩ.2.1 i)).differentiableAt
  have hDx : DifferentiableAt ℝ (fun a => mixedSourceDisplacement J q f r τ lam s background t a) x := by
    have hh := (mixedSourceDisplacement_contDiffAt J j q f hr τ lam s background t x hp hm hΩ).differentiableAt (by simp)
    exact hh.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hAx := (hF.restrictScalars ℝ).comp x hDx
  have hEx := (mixedHybridVolume_spatial_differentiable J f hr τ lam t (mixedFreeze (insert q J) background x)
    hp hm (fun i _ => hΩ.2.1 i)).comp x ((mixedFreeze_contDiff (insert q J) background).differentiable (by simp) x)
  exact ⟨hEs.mul hAs,hEx.mul hAx⟩

theorem mixed_frozen_regular_lie {n : ℕ}
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (hj : j∈J) (hq : q∉J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ)
    (s : ℂ) (background : Fin (n+1) → ℝ) (t : ℂ) (x : Fin (n+1) → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hpval : ∀ i∈insert q J,f.p (x i)=f.p (background i))
    (hmval : ∀ i∈insert q J,f.m (x i)=f.m (background i))
    (hplateau : ∀ i∈insert q J,deriv f.p (mixedFreeze (insert q J) background x i)=0 ∧
      deriv f.m (mixedFreeze (insert q J) background x i)=0)
    (hbranch : ∀ i∈J,Real.sin (mixedFreeze (insert q J) background x i)<0)
    (hΩ : (t,mixedFreeze (insert q J) background x)∈mixedSeparatedDomain J j q f r τ lam)
    (F : MixedActiveSpace (n+1) → ℂ)
    (hF : DifferentiableAt ℂ F (mixedSourceDisplacement J q f r τ lam s background t x))
    (hdiv : mixedHybridDivergence J j q f r τ lam t (mixedFreeze (insert q J) background x)=
      fderiv ℂ (mixedActiveBranchResidual J j q s
        (fun i => mixedContourPhase f r τ lam s background i) (deformedPoint f r τ lam background))
        (mixedSourceDisplacement J q f r τ lam s background t x) (mixedActiveBranchDirection j)+
      fderiv ℂ (mixedActiveCompactResidual J j q s
        (fun i => mixedContourPhase f r τ lam s background i) (deformedPoint f r τ lam background))
        (mixedSourceDisplacement J q f r τ lam s background t x) (mixedActiveCompactDirection (n+1))) :
    let φ := fun i => mixedContourPhase f r τ lam s background i
    let y := deformedPoint f r τ lam background
    IsingBulk.Lie.lieStep (fun z a => mixedContourVelocity J j q f r τ lam z (mixedFreeze (insert q J) background a))
      (mixedRegularPullback J q f r τ lam s background F) t x=
      mixedRegularPullback J q f r τ lam s background
        (mixedRegularDensityStep (mixedActiveParameterDirection (n+1)) (mixedActiveBranchDirection j)
          (mixedActiveCompactDirection (n+1)) (mixedActiveBranchResidual J j q s φ y)
          (mixedActiveCompactResidual J j q s φ y) F) t x := by
  let θ := mixedFreeze (insert q J) background x
  let V := mixedContourVelocity J j q f r τ lam
  let V' := fun z a => V z (mixedFreeze (insert q J) background a)
  let A := fun z a => F (mixedSourceDisplacement J q f r τ lam s background z a)
  let E := mixedHybridVolume J f r τ lam
  let E' := fun z a => E z (mixedFreeze (insert q J) background a)
  have hfz := (mixedFreeze_contDiff (insert q J) background).differentiable (by simp) x
  have hVs (i : Fin (n+1)) : DifferentiableAt ℝ (fun z => V t z i) θ :=
    (mixedSeparated_velocity_smooth J j q f hr τ lam hp hm i).angular_differentiableAt hΩ
  have hV' (i : Fin (n+1)) : DifferentiableAt ℝ (fun z => V' t z i) x := by
    have hh := (hVs i).comp x hfz
    exact hh
  have hEs : DifferentiableAt ℂ (fun z => E' z x) t :=
    (mixedHybridVolume_parameter J f r τ lam t θ hΩ.1 (fun i _ => hΩ.2.1 i)).differentiableAt
  have hEx : DifferentiableAt ℝ (E t) θ :=
    mixedHybridVolume_spatial_differentiable J f hr τ lam t θ hp hm (fun i _ => hΩ.2.1 i)
  have hE'x : DifferentiableAt ℝ (E' t) x := by
    have hh := hEx.comp x hfz
    exact hh
  have hAs : DifferentiableAt ℂ (fun z => A z x) t :=
    (hF.hasFDerivAt.comp_hasDerivAt t
      (mixedSourceDisplacement_parameter J q f r τ lam s background t x hΩ.1 (fun i _ => hΩ.2.1 i))).differentiableAt
  have hDx : DifferentiableAt ℝ (fun a => mixedSourceDisplacement J q f r τ lam s background t a) x := by
    have hh := (mixedSourceDisplacement_contDiffAt J j q f hr τ lam s background t x hp hm hΩ).differentiableAt (by simp)
    exact hh.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hAx : DifferentiableAt ℝ (A t) x := (hF.restrictScalars ℝ).comp x hDx
  have hE : IsingBulk.Lie.lieStep V' E' t x=E' t x*mixedHybridDivergence J j q f r τ lam t θ := by
    rw [lieStep_mixedFreeze (insert q J) background V E
      (mixed_velocity_active_support J j q f r τ lam hj) t x (fun i => (hVs i).mul hEx)]
    apply mixedHybridVolume_lie J j q f hr τ lam t θ hj hΩ.1 hp hm
      (fun i hi => hplateau i (by rcases hi with hi | hi; exact Finset.mem_insert_of_mem hi; simp [hi]))
      (fun i _ => hΩ.2.1 i) _ hVs
    intro i hi
    unfold mixedSourceSlope
    exact div_ne_zero (mul_ne_zero Complex.I_ne_zero (hΩ.2.2.1 i hi))
      (mul_ne_zero (by norm_num) (mixedSourcePhase_sin_ne (hΩ.2.1 i)))
  have hA := mixed_frozen_scalar_transport (Nat.succ_pos n) J j q hj hq f hr τ lam s background t x hpval hmval
    (fun _ => hp.differentiable (by simp) _) (fun _ => hm.differentiable (by simp) _)
    hplateau hbranch hΩ F hF
  dsimp only at hA ⊢
  have he : mixedRegularPullback J q f r τ lam s background F=fun z a => A z a*E' z a := by
    funext z a
    exact mul_comm _ _
  rw [he,IsingBulk.Lie.lieStep_product_rule V' A E' t x hAs hEs hAx hE'x hV',hE,
    ← mixedCoordinateTransport_eq_lie V' A t x hAx,hA,hdiv]
  dsimp only [mixedRegularPullback,mixedRegularDensityStep,A,E',E]
  dsimp only [mixedContourPhase] at *
  ring

end
end IsingBulk.Tail
