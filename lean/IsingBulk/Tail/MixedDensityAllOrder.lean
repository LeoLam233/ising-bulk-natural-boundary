import IsingBulk.Tail.MixedCutoffGerm

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Every finite source Lie iterate has the already bounded sparse term
expansion. The induction uses joint germs, not isolated point identities. -/
theorem mixedDensityJetTerms_all_order_germ {n : ℕ}
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
    (hV : ∀ i,AnalyticAt ℂ (mixedActiveAngularVelocity J j q s
      (fun i => mixedContourPhase f r τ lam s background i) (deformedPoint f r τ lam background) i) 0)
    (C : ℂ) (w : (Fin (n+1) → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w)
    (F : MixedActiveSpace (n+1) → ℂ) (hF : AnalyticAt ℂ F 0) (k : ℕ) :
    let φ := fun i => mixedContourPhase f r τ lam s background i
    let y := deformedPoint f r τ lam background
    Function.uncurry ((IsingBulk.Lie.lieStep
      (fun z a => mixedContourVelocity J j q f r τ lam z (mixedFreeze (insert q J) background a)))^[k]
      (fun z a => (w (mixedFreeze (insert q J) background a):ℂ)*
        mixedAnalyticDensityModel J q f r τ lam s background C F z a)) =ᶠ[𝓝 (s,background)]
    (fun p => ((mixedDensityJetTerms (mixedActiveParameterDirection (n+1)) (mixedActiveBranchDirection j)
      (mixedActiveCompactDirection (n+1)) (mixedActiveBranchResidual J j q s φ y)
      (mixedActiveCompactResidual J j q s φ y) F (mixedActiveAngularVelocity J j q s φ y) k).map
        (fun T => T.sourceValue J q f r τ lam s background C w p.1 p.2)).sum) := by
  classical
  let φ := fun i => mixedContourPhase f r τ lam s background i
  let y := deformedPoint f r τ lam background
  let R₁ := mixedActiveBranchResidual J j q s φ y
  let R₂ := mixedActiveCompactResidual J j q s φ y
  let v := mixedActiveAngularVelocity J j q s φ y
  let V := fun z a => mixedContourVelocity J j q f r τ lam z (mixedFreeze (insert q J) background a)
  let L := mixedDensityJetTerms (mixedActiveParameterDirection (n+1)) (mixedActiveBranchDirection j)
    (mixedActiveCompactDirection (n+1)) R₁ R₂ F v
  have hdata := mixed_active_source_neighborhood J j q f hr τ lam s background hp_smooth hm_smooth hΩ hbranch hp hm
  have hdisp : Tendsto (fun p : ℂ × (Fin (n+1) → ℝ) =>
      mixedSourceDisplacement J q f r τ lam s background p.1 p.2) (𝓝 (s,background)) (𝓝 0) := by
    have hh := (mixedSourceDisplacement_contDiffAt J j q f hr τ lam s background s background hp_smooth hm_smooth
      (by simpa only [mixedFreeze_self] using hΩ)).continuousAt.tendsto
    simpa only [mixedSourceDisplacement_zero] using hh
  dsimp only
  induction k with
  | zero =>
    exact Filter.Eventually.of_forall (fun _ => by
      simp [mixedDensityJetTerms,MixedDensityJetTerm.sourceValue,cutoffJet,Function.uncurry])
  | succ k ih =>
    have ha : ∀ T∈L k,AnalyticAt ℂ T.regularPart 0 :=
      mixedDensityJetTerms_analytic _ _ _ R₁ R₂ F v 0 hR₁ hR₂ hV hF k
    have hanear : ∀ᶠ p : ℂ × (Fin (n+1) → ℝ) in 𝓝 (s,background),∀ T∈L k,
        AnalyticAt ℂ T.regularPart (mixedSourceDisplacement J q f r τ lam s background p.1 p.2) := by
      have hh := (Filter.eventually_all_finset (L k).toFinset).mpr (fun T hT =>
        hdisp.eventually (ha T (List.mem_toFinset.mp hT)).eventually_analyticAt)
      simpa only [List.mem_toFinset] using hh
    have hsnear : ∀ᶠ p : ℂ × (Fin (n+1) → ℝ) in 𝓝 (s,background),∀ T∈L k,
        IsingBulk.Lie.lieStep V (T.sourceValue J q f r τ lam s background C w) p.1 p.2=
        ((mixedDensityActions (n+1)).map (fun a =>
          (T.child (mixedActiveParameterDirection (n+1)) (mixedActiveBranchDirection j)
            (mixedActiveCompactDirection (n+1)) R₁ R₂ v a).sourceValue J q f r τ lam s background C w p.1 p.2)).sum := by
      have hh := (Filter.eventually_all_finset (L k).toFinset).mpr (fun T hT =>
        T.source_step_germ J j q hj hq f hr τ lam s background hp_smooth hm_smooth hΩ hbranch hp hm
          hR₁ hR₂ C w hw (ha T (List.mem_toFinset.mp hT)))
      simpa only [List.mem_toFinset,Function.uncurry,V,R₁,R₂,v,φ,y] using hh
    have ih' : Function.uncurry ((IsingBulk.Lie.lieStep V)^[k]
        (fun z a => (w (mixedFreeze (insert q J) background a):ℂ)*
          mixedAnalyticDensityModel J q f r τ lam s background C F z a)) =ᶠ[𝓝 (s,background)]
        Function.uncurry (fun z a => ((L k).map (fun T => T.sourceValue J q f r τ lam s background C w z a)).sum) := by
      filter_upwards [ih] with p hp
      exact hp
    have hnext := lieStep_joint_germ V s background ih'
    filter_upwards [hnext,hdata,hanear,hsnear] with p hnext hpdata hpA hpstep
    dsimp only [Function.uncurry] at hnext ⊢
    rw [Function.iterate_succ_apply']
    change IsingBulk.Lie.lieStep V _ p.1 p.2=_
    rw [hnext]
    have hVp (i : Fin (n+1)) : DifferentiableAt ℝ (fun a => V p.1 a i) p.2 := by
      have hh := (mixedSeparated_velocity_smooth J j q f hr τ lam hp_smooth hm_smooth i).angular_differentiableAt hpdata.1 |>.comp p.2
        ((mixedFreeze_contDiff (insert q J) background).differentiable (by simp) p.2)
      exact hh
    have hd (T : MixedDensityJetTerm (n+1) (MixedActiveSpace (n+1))) (hT : T∈L k) :=
      T.source_differentiable (Nat.succ_pos n) J j q f hr τ lam s background C w hw p.1 p.2
        hp_smooth hm_smooth hpdata.1 (hpA T hT).differentiableAt
    have he := lieStep_finite_sum V ((L k).map (fun T => T.sourceValue J q f r τ lam s background C w)) p.1 p.2 hVp
      (by intro G hG; obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hG; exact (hd T hT).1)
      (by intro G hG; obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hG; exact (hd T hT).2)
    simp only [List.map_map,Function.comp_def] at he
    rw [he.2.2]
    simp only [mixedDensityJetTerms,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro T hT
    exact hpstep T hT

end
end IsingBulk.Tail
