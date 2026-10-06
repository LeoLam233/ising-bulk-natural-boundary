import IsingBulk.Tail.MixedDensityAllOrder
import IsingBulk.Tail.MixedIterateFreeze

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem iterate_lieStep_joint_germ {n : ℕ}
    (V : ℂ → (Fin (n+1) → ℝ) → Fin (n+1) → ℂ)
    {A B : ℂ → (Fin (n+1) → ℝ) → ℂ} (s : ℂ) (x : Fin (n+1) → ℝ)
    (h : Function.uncurry A =ᶠ[𝓝 (s,x)] Function.uncurry B) (k : ℕ) :
    Function.uncurry ((IsingBulk.Lie.lieStep V)^[k] A)=ᶠ[𝓝 (s,x)]
      Function.uncurry ((IsingBulk.Lie.lieStep V)^[k] B) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    simpa only [Function.iterate_succ_apply'] using lieStep_joint_germ V s x ih

/-- Exact finite expansion of the literal, unfrozen source density. The
normalization and coupled contour determinant are the original ones. -/
theorem mixed_actual_density_all_order {n : ℕ}
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (hj : j∈J) (hq : q∉J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin (n+1) → ℝ)
    (hp_smooth : ContDiff ℝ ∞ f.p) (hm_smooth : ContDiff ℝ ∞ f.m)
    (hΩ : (s,θ)∈mixedSeparatedDomain J j q f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (θ i)<0)
    (hp : ∀ i∈insert q J,f.p =ᶠ[𝓝 (θ i)] (fun _ => f.p (θ i)))
    (hm : ∀ i∈insert q J,f.m =ᶠ[𝓝 (θ i)] (fun _ => f.m (θ i)))
    (hR₁ : AnalyticAt ℂ (mixedActiveBranchResidual J j q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ)) 0)
    (hR₂ : AnalyticAt ℂ (mixedActiveCompactResidual J j q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ)) 0)
    (hV : ∀ i,AnalyticAt ℂ (mixedActiveAngularVelocity J j q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ) i) 0)
    (hF : AnalyticAt ℂ (mixedActiveRegularAmplitude J q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ)) 0)
    (w : (Fin (n+1) → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (k : ℕ) :
    let φ := fun i => mixedContourPhase f r τ lam s θ i
    let y := deformedPoint f r τ lam θ
    ((IsingBulk.Lie.lieStep (mixedContourVelocity J j q f r τ lam))^[k]
      (fun z a => (w a:ℂ)*pulledDensity f r τ lam z a)) s θ=
      ((mixedDensityJetTerms (mixedActiveParameterDirection (n+1)) (mixedActiveBranchDirection j)
        (mixedActiveCompactDirection (n+1)) (mixedActiveBranchResidual J j q s φ y)
        (mixedActiveCompactResidual J j q s φ y) (mixedActiveRegularAmplitude J q s φ y)
        (mixedActiveAngularVelocity J j q s φ y) k).map
        (fun T => T.sourceValue J q f r τ lam s θ (mixedDensityNormalization f τ lam θ) w s θ)).sum := by
  let F := mixedActiveRegularAmplitude J q s (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ)
  let C := mixedDensityNormalization f τ lam θ
  let V := fun z a => mixedContourVelocity J j q f r τ lam z (mixedFreeze (insert q J) θ a)
  have hd := mixed_pulledDensity_active_germ J j q f hr τ lam s θ hp_smooth hm_smooth hΩ hbranch hp hm
  simp_rw [mixedFrozenDensityModel_eq_analytic] at hd
  have hi : Function.uncurry (fun z a => (w (mixedFreeze (insert q J) θ a):ℂ)*
      pulledDensity f r τ lam z (mixedFreeze (insert q J) θ a)) =ᶠ[𝓝 (s,θ)]
      Function.uncurry (fun z a => (w (mixedFreeze (insert q J) θ a):ℂ)*
        mixedAnalyticDensityModel J q f r τ lam s θ C F z a) := by
    filter_upwards [hd] with p hp
    exact congrArg (fun a => (w (mixedFreeze (insert q J) θ p.2):ℂ)*a) hp
  have he := mixedDensityJetTerms_all_order_germ J j q hj hq f hr τ lam s θ hp_smooth hm_smooth hΩ hbranch hp hm
    hR₁ hR₂ hV C w hw F hF k
  have hjoined := ((iterate_lieStep_joint_germ V s θ hi k).trans he).eq_of_nhds
  have hwc : ContDiff ℝ ∞ (fun a => (w a:ℂ)) := Complex.ofRealCLM.contDiff.comp hw
  have hf := mixed_actual_weighted_iterate_freeze J j q hj f hr τ lam hp_smooth hm_smooth _ hwc s θ hΩ k
  dsimp only [Function.uncurry] at hjoined
  rw [hf] at hjoined
  exact hjoined

end
end IsingBulk.Tail
