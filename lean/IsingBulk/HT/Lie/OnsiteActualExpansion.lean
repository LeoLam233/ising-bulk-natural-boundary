import IsingBulk.HT.Lie.OnsiteModelSmooth
import IsingBulk.Tail.MixedActualDensityExpansion

/-! Exact all-order expansion of the literal onsite source. The actual
source is identified on branch-active germs and the freeze restriction is
removed by smooth local Lie calculus. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Jets IsingBulk.Lie IsingBulk.HT.Contour Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem onsite_actual_density_all_order {n : ℕ}
    (J : Finset (Fin (n+1))) (q : Fin (n+1)) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (x : Fin (n+1) → ℝ)
    (hp_smooth : ContDiff ℝ ∞ f.p) (hm_smooth : ContDiff ℝ ∞ f.m)
    (hΩ : (s,x)∈onsiteLieDomain J f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (x i)<0)
    (hp : ∀ i∈J,f.p =ᶠ[𝓝 (x i)] fun _ => f.p (x i))
    (hm : ∀ i∈J,f.m =ᶠ[𝓝 (x i)] fun _ => f.m (x i))
    (hV : ∀ i,AnalyticAt ℂ (onsiteActiveVelocity J s
      (fun i => mixedContourPhase f r τ lam s x i) i) 0)
    (hF : AnalyticAt ℂ (onsiteActiveRegularAmplitude J q s
      (fun i => mixedContourPhase f r τ lam s x i) (deformedPoint f r τ lam x)) 0)
    (w : (Fin (n+1) → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (k : ℕ) :
    let φ := fun i => mixedContourPhase f r τ lam s x i
    let F := fun u => mixedDensityNormalization f τ lam x*
      onsiteActiveRegularAmplitude J q s φ (deformedPoint f r τ lam x) u
    ((lieStep (onsiteBranchField J f r τ lam))^[k]
      (fun t a => (w a:ℂ)*onsitePulledDensity f r τ lam t a)) s x=
      ((onsiteJetTerms J s φ F k).map (fun T => T.onsiteValue J f r τ lam s φ w s x)).sum := by
  let φ := fun i => mixedContourPhase f r τ lam s x i
  let F := fun u => mixedDensityNormalization f τ lam x*
    onsiteActiveRegularAmplitude J q s φ (deformedPoint f r τ lam x) u
  let V := onsiteBranchField J f r τ lam
  let Vf := fun t a => V t (mixedFreeze J x a)
  let M := onsiteRegularModel J f r τ lam s φ F
  have hFa : AnalyticAt ℂ F 0 := analyticAt_const.mul hF
  have hd := onsite_source_active_germ J q f hr τ lam s x hp_smooth hm_smooth hΩ hbranch hp hm
  have hi : Function.uncurry (fun t a => (w (mixedFreeze J x a):ℂ)*
      onsitePulledDensity f r τ lam t (mixedFreeze J x a)) =ᶠ[𝓝 (s,x)]
      Function.uncurry (fun t a => (w (mixedFreeze J x a):ℂ)*M t (mixedFreeze J x a)) := by
    filter_upwards [hd] with p hp
    exact congrArg (fun a => (w (mixedFreeze J x p.2):ℂ)*a) hp
  have hjoined := (iterate_lieStep_joint_germ Vf s x hi k).eq_of_nhds
  have hwc : ContDiff ℝ ∞ (fun a => (w a:ℂ)) := Complex.ofRealCLM.contDiff.comp hw
  have hsupport : ∀ i,i∉J → ∀ t a,V t a i=0 := by
    intro i hi t a
    exact onsiteBranchField_of_not_mem J f r τ lam t a i hi
  have hfreezeSource := lieStep_iterate_mixedFreeze J x V
    (fun t a => (w a:ℂ)*onsitePulledDensity f r τ lam t a) (onsiteLieDomain J f r τ lam)
    (onsiteLieDomain_isOpen J f hr τ lam hp_smooth hm_smooth) hsupport
    (fun i => onsiteLie_field_smooth J f hr τ lam hp_smooth hm_smooth i)
    (fun l => onsite_weighted_lie_stages_smooth J f hr τ lam hp_smooth hm_smooth _ hwc l)
    k s x (by simpa only [mixedFreeze_self] using hΩ)
  let U := onsiteModelDomain J f r τ lam s φ F
  have hU := onsiteModelDomain_isOpen J f hr τ lam s φ hp_smooth hm_smooth F
  have hVsm (i : Fin (n+1)) : ParameterSmoothOn U (fun t a => V t a i) :=
    fun p hp => onsiteLie_field_smooth J f hr τ lam hp_smooth hm_smooth i p hp.1
  have hMsm : ParameterSmoothOn U (fun t a => (w a:ℂ)*M t a) :=
    (ParameterSmoothOn.angular U _ hwc).mul
      (onsiteRegularModel_smooth J f hr τ lam s φ hp_smooth hm_smooth F)
  have hfreezeModel := lieStep_iterate_mixedFreeze J x V (fun t a => (w a:ℂ)*M t a) U hU
    hsupport hVsm (fun l => hMsm.iterate_lieStep hU V _ hVsm l) k s x
    (by refine ⟨?_,?_⟩
        · simpa only [mixedFreeze_self] using hΩ
        · simpa only [mixedFreeze_self,Set.mem_ofPred_eq,φ,onsiteDisplacement_base] using hFa)
  have hexp := (onsiteJetTerms_all_order_germ J f hr τ lam s x hp_smooth hm_smooth hΩ
    hbranch hp hm hV w hw F hFa k).eq_of_nhds
  dsimp only [Function.uncurry] at hjoined hexp
  rw [hfreezeSource,hfreezeModel] at hjoined
  simp only [mixedFreeze_self] at hjoined
  exact hjoined.trans hexp

end
end IsingBulk.HT.Lie
