import IsingBulk.Tail.MixedCutoffDifferential

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def MixedDensityJetTerm.sourceValue {N : ℕ} (T : MixedDensityJetTerm N (MixedActiveSpace N))
    (J : Finset (Fin N)) (q : Fin N) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (background : Fin N → ℝ) (C : ℂ) (w : (Fin N → ℝ) → ℝ)
    (t : ℂ) (x : Fin N → ℝ) : ℂ :=
  (cutoffJet T.cutoff w (mixedFreeze (insert q J) background x):ℂ)*
    mixedAnalyticDensityModel J q f r τ lam s background C T.regularPart t x

theorem mixedDensityActions_sum {N : ℕ} (F : Option (Fin N) → ℂ) :
    ((mixedDensityActions N).map F).sum=F none+∑ i,F (some i) := by
  simp [mixedDensityActions,Function.comp_def,List.finRange,List.sum_ofFn]

theorem MixedDensityJetTerm.source_differentiable {N : ℕ} (hN : 0<N)
    (T : MixedDensityJetTerm N (MixedActiveSpace N)) (J : Finset (Fin N)) (j q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (background : Fin N → ℝ)
    (C : ℂ) (w : (Fin N → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (t : ℂ) (x : Fin N → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hΩ : (t,mixedFreeze (insert q J) background x)∈mixedSeparatedDomain J j q f r τ lam)
    (hT : DifferentiableAt ℂ T.regularPart (mixedSourceDisplacement J q f r τ lam s background t x)) :
    DifferentiableAt ℂ (fun z => T.sourceValue J q f r τ lam s background C w z x) t ∧
    DifferentiableAt ℝ (T.sourceValue J q f r τ lam s background C w t) x := by
  have hM := mixedAnalyticDensityModel_differentiable hN J j q f hr τ lam s background t x hp hm hΩ C T.regularPart hT
  have hW : DifferentiableAt ℝ (fun a => (cutoffJet T.cutoff w (mixedFreeze (insert q J) background a):ℂ)) x := by
    have hh := (Complex.ofRealCLM.differentiableAt.comp _
      ((cutoffJet_contDiff T.cutoff w hw).differentiable (by simp) (mixedFreeze (insert q J) background x))).comp x
        ((mixedFreeze_contDiff (insert q J) background).differentiable (by simp) x)
    exact hh
  exact ⟨hM.1.const_mul _,hW.mul hM.2⟩

/-- A real cutoff produces every angular child. Its derivatives remain on
the real contour, while the velocity multiplies the analytic regular part. -/
theorem MixedDensityJetTerm.source_step {n : ℕ}
    (T : MixedDensityJetTerm (n+1) (MixedActiveSpace (n+1)))
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (hj : j∈J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (background : Fin (n+1) → ℝ)
    (C : ℂ) (w : (Fin (n+1) → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (t : ℂ) (x : Fin (n+1) → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hΩ : (t,mixedFreeze (insert q J) background x)∈mixedSeparatedDomain J j q f r τ lam)
    (hT : DifferentiableAt ℂ T.regularPart (mixedSourceDisplacement J q f r τ lam s background t x))
    (R₁ R₂ : MixedActiveSpace (n+1) → ℂ) (V : Fin (n+1) → MixedActiveSpace (n+1) → ℂ)
    (hVmodel : ∀ i,mixedContourVelocity J j q f r τ lam t (mixedFreeze (insert q J) background x) i=
      V i (mixedSourceDisplacement J q f r τ lam s background t x))
    (hstep : IsingBulk.Lie.lieStep
      (fun z a => mixedContourVelocity J j q f r τ lam z (mixedFreeze (insert q J) background a))
      (mixedAnalyticDensityModel J q f r τ lam s background C T.regularPart) t x=
      mixedAnalyticDensityModel J q f r τ lam s background C
        (mixedRegularDensityStep (mixedActiveParameterDirection (n+1)) (mixedActiveBranchDirection j)
          (mixedActiveCompactDirection (n+1)) R₁ R₂ T.regularPart) t x) :
    IsingBulk.Lie.lieStep
      (fun z a => mixedContourVelocity J j q f r τ lam z (mixedFreeze (insert q J) background a))
      (T.sourceValue J q f r τ lam s background C w) t x=
      ((mixedDensityActions (n+1)).map (fun a =>
        (T.child (mixedActiveParameterDirection (n+1)) (mixedActiveBranchDirection j)
          (mixedActiveCompactDirection (n+1)) R₁ R₂ V a).sourceValue J q f r τ lam s background C w t x)).sum := by
  let θ := mixedFreeze (insert q J) background x
  let W := mixedContourVelocity J j q f r τ lam
  let W' := fun z a => W z (mixedFreeze (insert q J) background a)
  let M := mixedAnalyticDensityModel J q f r τ lam s background C T.regularPart
  have hfz := (mixedFreeze_contDiff (insert q J) background).differentiable (by simp) x
  have hW (i : Fin (n+1)) : DifferentiableAt ℝ (fun a => W' t a i) x := by
    have hh := (mixedSeparated_velocity_smooth J j q f hr τ lam hp hm i).angular_differentiableAt hΩ |>.comp x hfz
    exact hh
  have hM := mixedAnalyticDensityModel_differentiable (Nat.succ_pos n) J j q f hr τ lam s background t x hp hm hΩ C T.regularPart hT
  have hwθ := (cutoffJet_contDiff T.cutoff w hw).differentiable (by simp) θ
  have hwx := hwθ.comp x hfz
  have he := IsingBulk.Lie.lieStep_real_weight W'
    (fun a => cutoffJet T.cutoff w (mixedFreeze (insert q J) background a)) M t x hwx hM.1 hM.2 hW
  change IsingBulk.Lie.lieStep W' (T.sourceValue J q f r τ lam s background C w) t x=_ at he
  rw [hstep,mixed_cutoff_transport (insert q J) background x W t
    (fun i hi => mixed_velocity_active_support J j q f r τ lam hj i hi t θ) _ hwθ] at he
  rw [he,mixedDensityActions_sum]
  have hc (i : Fin (n+1)) :
      (T.child (mixedActiveParameterDirection (n+1)) (mixedActiveBranchDirection j)
        (mixedActiveCompactDirection (n+1)) R₁ R₂ V (some i)).sourceValue J q f r τ lam s background C w t x=
      -(W t θ i*(cutoffJet (i::T.cutoff) w θ:ℂ)*M t x) := by
    dsimp only [MixedDensityJetTerm.child,MixedDensityJetTerm.sourceValue,mixedAnalyticDensityModel,
      mixedRegularPullback,M,W,θ]
    rw [hVmodel i]
    ring
  simp_rw [hc]
  rw [Finset.sum_neg_distrib,← Finset.sum_mul]
  rfl

end
end IsingBulk.Tail
