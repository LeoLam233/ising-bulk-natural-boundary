import IsingBulk.HT.Lie.OnsiteSourceGerm

/-! All-order onsite Lie expansion. The field depends on the temperature
at every stage. Sparse children contain only fixed-phase parameter jets
and real cutoff jets; all hybrid residuals are exactly zero. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Jets IsingBulk.Lie IsingBulk.HT.Contour Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

theorem onsiteDisplacement_continuousAt {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (φ : Fin N → ℂ)
    (p : ℂ × (Fin N → ℝ)) (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hΩ : p∈onsiteLieDomain J f r τ lam) :
    ContinuousAt (fun z : ℂ × (Fin N → ℝ) => onsiteDisplacement J f r τ lam s φ z.1 z.2) p := by
  have hphase (i : Fin N) : ContinuousAt (fun z : ℂ × (Fin N → ℝ) =>
      mixedContourPhase f r τ lam z.1 z.2 i) p :=
    (((onsiteLie_W_smooth J f hr τ lam hp hm i).complex_comp lowerArccos
      (fun z hz => lowerArccos_analytic_upper (hz.2.1 i))) p hΩ).1.continuousAt
  unfold onsiteDisplacement onsiteModelMap
  apply ContinuousAt.prodMk (continuous_fst.continuousAt.sub continuousAt_const)
  apply ContinuousAt.prodMk _ continuousAt_const
  apply continuousAt_pi.mpr
  intro i
  by_cases hi : i∈J
  · simp only [mixedHybridMap,hi,ite_true]
    convert (hphase i).sub (continuousAt_const (y := φ i)) using 1
  · simp only [hi,ite_false]
    exact continuousAt_const

theorem onsite_plateau_neighborhood {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (x : Fin N → ℝ)
    (hp_smooth : ContDiff ℝ ∞ f.p) (hm_smooth : ContDiff ℝ ∞ f.m)
    (hΩ : (s,x)∈onsiteLieDomain J f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (x i)<0)
    (hp : ∀ i∈J,f.p =ᶠ[𝓝 (x i)] fun _ => f.p (x i))
    (hm : ∀ i∈J,f.m =ᶠ[𝓝 (x i)] fun _ => f.m (x i)) :
    ∀ᶠ z : ℂ × (Fin N → ℝ) in 𝓝 (s,x),
      z∈onsiteLieDomain J f r τ lam ∧
      (∀ i∈J,Real.sin (z.2 i)<0) ∧
      ∀ i∈J,deriv f.p (z.2 i)=0 ∧ deriv f.m (z.2 i)=0 := by
  have hbnear : ∀ᶠ y in 𝓝 x,∀ i∈J,Real.sin (y i)<0 := by
    apply (Filter.eventually_all_finset J).mpr
    intro i hi
    exact (Real.continuous_sin.comp (continuous_apply i)).continuousAt.eventually_lt
      continuousAt_const (hbranch i hi)
  have hsnd : Tendsto (fun z : ℂ × (Fin N → ℝ) => z.2) (𝓝 (s,x)) (𝓝 x) :=
    continuous_snd.continuousAt.tendsto
  filter_upwards [(onsiteLieDomain_isOpen J f hr τ lam hp_smooth hm_smooth).mem_nhds hΩ,
    hsnd.eventually hbnear,hsnd.eventually (mixed_plateau_data_eventually J x f.p hp),
    hsnd.eventually (mixed_plateau_data_eventually J x f.m hm)] with z hzΩ hzb hzp hzm
  refine ⟨hzΩ,hzb,?_⟩
  intro i hi
  exact ⟨(hzp i hi).2.trans (by simpa only [deriv_const] using (hp i hi).deriv_eq),
    (hzm i hi).2.trans (by simpa only [deriv_const] using (hm i hi).deriv_eq)⟩

theorem onsiteJetTerms_all_order_germ {n : ℕ}
    (J : Finset (Fin (n+1))) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (x : Fin (n+1) → ℝ)
    (hp_smooth : ContDiff ℝ ∞ f.p) (hm_smooth : ContDiff ℝ ∞ f.m)
    (hΩ : (s,x)∈onsiteLieDomain J f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (x i)<0)
    (hp : ∀ i∈J,f.p =ᶠ[𝓝 (x i)] fun _ => f.p (x i))
    (hm : ∀ i∈J,f.m =ᶠ[𝓝 (x i)] fun _ => f.m (x i))
    (hV : ∀ i,AnalyticAt ℂ (onsiteActiveVelocity J s
      (fun i => mixedContourPhase f r τ lam s x i) i) 0)
    (w : (Fin (n+1) → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w)
    (F : MixedActiveSpace (n+1) → ℂ) (hF : AnalyticAt ℂ F 0) (k : ℕ) :
    let φ := fun i => mixedContourPhase f r τ lam s x i
    Function.uncurry ((lieStep (onsiteBranchField J f r τ lam))^[k]
      (fun t a => (w a:ℂ)*onsiteRegularModel J f r τ lam s φ F t a)) =ᶠ[𝓝 (s,x)]
    (fun p => ((onsiteJetTerms J s φ F k).map
      (fun T => T.onsiteValue J f r τ lam s φ w p.1 p.2)).sum) := by
  classical
  let φ := fun i => mixedContourPhase f r τ lam s x i
  let V := onsiteBranchField J f r τ lam
  let L := onsiteJetTerms J s φ F
  have hdata := onsite_plateau_neighborhood J f hr τ lam s x hp_smooth hm_smooth hΩ hbranch hp hm
  have hdisp : Tendsto (fun p : ℂ × (Fin (n+1) → ℝ) =>
      onsiteDisplacement J f r τ lam s φ p.1 p.2) (𝓝 (s,x)) (𝓝 0) := by
    simpa only [φ,onsiteDisplacement_base] using
      (onsiteDisplacement_continuousAt J f hr τ lam s φ (s,x) hp_smooth hm_smooth hΩ).tendsto
  dsimp only
  induction k with
  | zero =>
    exact Eventually.of_forall (fun _ => by
      simp [onsiteJetTerms,mixedDensityJetTerms,MixedDensityJetTerm.onsiteValue,cutoffJet,Function.uncurry])
  | succ k ih =>
    have ha : ∀ T∈L k,AnalyticAt ℂ T.regularPart 0 :=
      mixedDensityJetTerms_analytic _ _ _ (fun _ => 0) (fun _ => 0) F
        (onsiteActiveVelocity J s φ) 0 analyticAt_const analyticAt_const hV hF k
    have hanear : ∀ᶠ p : ℂ × (Fin (n+1) → ℝ) in 𝓝 (s,x),∀ T∈L k,
        AnalyticAt ℂ T.regularPart (onsiteDisplacement J f r τ lam s φ p.1 p.2) := by
      have hh := (Filter.eventually_all_finset (L k).toFinset).mpr (fun T hT =>
        hdisp.eventually (ha T (List.mem_toFinset.mp hT)).eventually_analyticAt)
      simpa only [List.mem_toFinset] using hh
    have ih' : Function.uncurry ((lieStep V)^[k]
        (fun t a => (w a:ℂ)*onsiteRegularModel J f r τ lam s φ F t a)) =ᶠ[𝓝 (s,x)]
        Function.uncurry (fun t a => ((L k).map (fun T => T.onsiteValue J f r τ lam s φ w t a)).sum) := ih
    have hnext := lieStep_joint_germ V s x ih'
    filter_upwards [hnext,hdata,hanear] with p hnext hpdata hpA
    dsimp only [Function.uncurry] at hnext ⊢
    rw [Function.iterate_succ_apply']
    change lieStep V _ p.1 p.2=_
    rw [hnext]
    have hVp (i : Fin (n+1)) : DifferentiableAt ℝ (fun a => V p.1 a i) p.2 :=
      onsiteBranchField_spatial_differentiable J f hr τ lam p.1 p.2 hp_smooth hm_smooth hpdata.1.2.2 i
    have hd (T : MixedDensityJetTerm (n+1) (MixedActiveSpace (n+1))) (hT : T∈L k) :
        DifferentiableAt ℂ (fun t => T.onsiteValue J f r τ lam s φ w t p.2) p.1 ∧
        DifferentiableAt ℝ (T.onsiteValue J f r τ lam s φ w p.1) p.2 := by
      have hM := onsiteRegularModel_differentiable J f hr τ lam s φ p.1 p.2 hpdata.1.1
        hp_smooth hm_smooth (fun i _ => hpdata.1.2.1 i) T.regularPart (hpA T hT).differentiableAt
      have hcut := Complex.ofRealCLM.differentiableAt.comp p.2
        ((cutoffJet_contDiff T.cutoff w hw).differentiable (by simp) p.2)
      exact ⟨hM.1.const_mul _,hcut.mul hM.2⟩
    have he := lieStep_finite_sum V ((L k).map (fun T => T.onsiteValue J f r τ lam s φ w)) p.1 p.2 hVp
      (by intro G hG; obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hG; exact (hd T hT).1)
      (by intro G hG; obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hG; exact (hd T hT).2)
    simp only [List.map_map,Function.comp_def] at he
    rw [he.2.2]
    simp only [onsiteJetTerms,mixedDensityJetTerms,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro T hT
    exact T.onsite_step J f hr τ lam s φ p.1 p.2 hpdata.1.1 hp_smooth hm_smooth
      hpdata.2.2 hpdata.2.1 (fun i _ => hpdata.1.2.1 i) hpdata.1.2.2 w hw (hpA T hT).differentiableAt

end
end IsingBulk.HT.Lie
