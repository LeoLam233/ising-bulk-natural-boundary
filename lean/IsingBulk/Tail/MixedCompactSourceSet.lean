import IsingBulk.Tail.MixedRationalCoefficients
import IsingBulk.Tail.MixedSourceGeometry
import Mathlib.Topology.MetricSpace.Thickening

/-! A fixed compact analytic source-pair neighborhood for EVERY actual
compact coordinate. It is chosen before N and the coupled occupancy. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Metric
open scoped Topology

def mixedRootPairDomain : Set (ℂ × ℂ) :=
  {p | p.1≠0 ∧ p.2≠0 ∧ sourceW p.1 p.2 ∈ continuedRootDomain}

theorem mixedRootPairDomain_isOpen : IsOpen mixedRootPairDomain := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hs : ContinuousAt (fun q : ℂ × ℂ => q.1+q.1⁻¹) p :=
    continuous_fst.continuousAt.add (continuous_fst.continuousAt.inv₀ hp.1)
  have hy : ContinuousAt (fun q : ℂ × ℂ => q.2+q.2⁻¹) p :=
    continuous_snd.continuousAt.add (continuous_snd.continuousAt.inv₀ hp.2.1)
  have hw : ContinuousAt (fun q : ℂ × ℂ => sourceW q.1 q.2) p := hs.sub (hy.div_const 2)
  filter_upwards [continuous_fst.continuousAt.eventually_ne hp.1,
    continuous_snd.continuousAt.eventually_ne hp.2.1,
    hw.preimage_mem_nhds (continuedRootDomain_isOpen.mem_nhds hp.2.2)] with q hqS hqY hqW
  exact ⟨hqS,hqY,hqW⟩

theorem sourceW_limitingAngle (d : LocalBranchData) (θ : ℝ) :
    sourceW (radialParameter d.theta 0) (limitingAngle θ)=(limitingAngularW d.thetaB θ:ℂ) := by
  unfold sourceW
  rw [sourceS_radial_zero_branch,limitingAngle_trace]
  unfold limitingAngularW
  push_cast
  ring

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
theorem actual_compact_source_pair_set (d : LocalBranchData) (inner : ℝ) (hi : 0< inner) :
    ∃ (K : Set (ℂ × ℂ)) (c e t₀ : ℝ), IsCompact K ∧ K⊆mixedRootPairDomain ∧
      0<c ∧ 0<e ∧ 0<t₀ ∧ ∀ (f : SelectorFunctions),
      (∀ x,0≤f.p x ∧ f.p x≤1) → (∀ x,0≤f.m x ∧ f.m x≤1) →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) (s : ℂ),
        1≤N → 0≤eps → eps≤e → 0≤τ → 0≤lam → lam≤1 → lam*τ≤t₀ →
        θ i∈Icc 0 (2*Real.pi) → inner/2≤|sectorDisplacement d.thetaB (θ i)| →
        ‖s-radialParameter d.theta eps‖≤c*eps →
        (s,deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)∈K := by
  let A : Set ℝ := Icc 0 (2*Real.pi) ∩ {θ | inner/2≤|sectorDisplacement d.thetaB θ|}
  have hA : IsCompact A := isCompact_Icc.inter_right (isClosed_le continuous_const (by unfold sectorDisplacement; fun_prop))
  let F := fun θ : ℝ => (radialParameter d.theta 0,limitingAngle θ)
  have hF : Continuous F := by unfold F limitingAngle; fun_prop
  let K₀ := F '' A
  have hK₀ : IsCompact K₀ := hA.image hF
  have hS : 0<1+Real.cos d.thetaB := by
    have hh := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,d.theta_pos],d.theta_lt⟩
    linarith [d.angle_relation]
  have hK₀D : K₀⊆mixedRootPairDomain := by
    rintro p ⟨θ,hθ,rfl⟩
    refine ⟨?_,?_,?_⟩
    · exact norm_ne_zero_iff.mp (by rw [radialParameter_norm (by norm_num)]; norm_num)
    · exact norm_ne_zero_iff.mp (by rw [limitingAngle_norm]; norm_num)
    · change sourceW (radialParameter d.theta 0) (limitingAngle θ)∈continuedRootDomain
      rw [sourceW_limitingAngle]
      have hlo : -1<limitingAngularW d.thetaB θ := by unfold limitingAngularW; linarith [Real.cos_le_one θ]
      have hne : limitingAngularW d.thetaB θ≠1 := by
        intro he
        have hp : sectorDisplacement d.thetaB θ=0 := by unfold limitingAngularW at he; unfold sectorDisplacement; linarith
        have hh := hθ.2
        change inner/2≤|sectorDisplacement d.thetaB θ| at hh
        rw [hp,abs_zero] at hh
        linarith
      by_cases hw : 1<limitingAngularW d.thetaB θ
      · exact Or.inl (Or.inr (by simpa using hw))
      · exact Or.inr (by simpa using abs_lt.mpr ⟨hlo,lt_of_le_of_ne (le_of_not_gt hw) hne⟩)
  obtain ⟨r,hr,hsub⟩ := hK₀.exists_cthickening_subset_open mixedRootPairDomain_isOpen hK₀D
  obtain ⟨r',hr',hcomp⟩ := hK₀.exists_isCompact_cthickening
  let δ := min r r'
  have hδ : 0<δ := lt_min hr hr'
  let K := cthickening δ K₀
  have hK : IsCompact K := hcomp.of_isClosed_subset isClosed_cthickening (cthickening_mono (min_le_right _ _) K₀)
  have hKD : K⊆mixedRootPairDomain := (cthickening_mono (min_le_left _ _) K₀).trans hsub
  let e := min 1 (min (1/(4*(d.c₀+1))) (δ/(8*(d.c₀+1))))
  let t₀ := min (1/8:ℝ) (δ/16)
  have he : 0<e := by dsimp [e]; positivity [d.c₀_pos]
  have ht : 0<t₀ := lt_min (by norm_num) (by positivity)
  refine ⟨K,1/4,e,t₀,hK,hKD,by norm_num,he,ht,?_⟩
  intro f hp hm N eps τ lam θ i s hN heps hepsle hτ hl0 hl1 htl hθ hprofile hs
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have heps1 : eps≤1 := hepsle.trans (min_le_left _ _)
  have hepsbase := hepsle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsδ := hepsle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbase := (le_div_iff₀ (by positivity [d.c₀_pos] : 0<4*(d.c₀+1))).mp hepsbase
  have hδeps := (le_div_iff₀ (by positivity [d.c₀_pos] : 0<8*(d.c₀+1))).mp hepsδ
  have hτe : lam*τ≤1/8 := htl.trans (min_le_left _ _)
  have hτδ : lam*τ≤δ/16 := htl.trans (min_le_right _ _)
  let v := coupledRadialExponent d.c₀ eps (lam*τ) 1 (f.p (θ i)) (f.m (θ i))
    (occupancy (fun j => f.p (θ j))/(N:ℝ))
  have hvb : |v|≤d.c₀*eps+2*(lam*τ) := coupledRadialExponent_bound d.c₀_pos.le heps
    (mul_nonneg hl0 hτ) (by norm_num) (by norm_num) (hp _).1 (hp _).2 (hm _).1 (hm _).2
    (div_nonneg (occupancy_nonneg (fun j => (hp (θ j)).1)) hn.le)
    ((div_le_one hn).mpr (occupancy_le (fun j => (hp (θ j)).2)))
  have hv : |v|≤1 := hvb.trans (by nlinarith)
  have hy : deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i=radialAnglePoint v (θ i) := by
    rw [deformedPoint_scale_lambda,deformedPoint_coupledRadialExponent]
  have hdy : ‖deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i-limitingAngle (θ i)‖≤δ := by
    rw [hy]
    exact (radialAnglePoint_motion hv _).trans (by nlinarith [mul_nonneg d.c₀_pos.le heps])
  have hds : ‖s-radialParameter d.theta 0‖≤δ := by
    have hh := norm_sub_le_norm_sub_add_norm_sub s (radialParameter d.theta eps) (radialParameter d.theta 0)
    rw [radialParameter_sub_zero_norm d.theta eps heps] at hh
    nlinarith [mul_nonneg d.c₀_pos.le heps]
  apply mem_cthickening_of_dist_le _ (F (θ i)) δ K₀ ⟨θ i,⟨hθ,hprofile⟩,rfl⟩
  change dist (s,deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)
    (radialParameter d.theta 0,limitingAngle (θ i))≤δ
  rw [Prod.dist_eq]
  simpa only [dist_eq_norm] using max_le hds hdy

/-- Actual scalar joint jets. This does not replace the separate chain-rule
bounds for pulling these jets through the coupled angular map. -/
theorem actual_compact_root_joint_jets (d : LocalBranchData) (inner : ℝ) (hi : 0< inner) :
    ∃ c e t₀ : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ ∀ J : ℕ,∃ C : ℝ,0<C ∧
      ∀ (f : SelectorFunctions), (∀ x,0≤f.p x ∧ f.p x≤1) → (∀ x,0≤f.m x ∧ f.m x≤1) →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) (s : ℂ),
        1≤N → 0≤eps → eps≤e → 0≤τ → 0≤lam → lam≤1 → lam*τ≤t₀ →
        θ i∈Icc 0 (2*Real.pi) → inner/2≤|sectorDisplacement d.thetaB (θ i)| →
        ‖s-radialParameter d.theta eps‖≤c*eps → ∀ k≤J,
        let p := (s,deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i)
        ‖iteratedFDeriv ℂ k (fun p : ℂ × ℂ => selectedContinuedRoot p.1 p.2) p‖≤C ∧
        ‖iteratedFDeriv ℂ k (fun p : ℂ × ℂ => mixedRootSlope p.1 p.2) p‖≤C ∧
        ‖iteratedFDeriv ℂ k (fun p : ℂ × ℂ => mixedRootTau p.1 p.2) p‖≤C := by
  obtain ⟨K,c,e,t₀,hK,hKD,hc,he,ht,hcover⟩ := actual_compact_source_pair_set d inner hi
  refine ⟨c,e,t₀,hc,he,ht,?_⟩
  intro J
  obtain ⟨C,hC,hRoot⟩ := compact_finite_analytic_jets K hK
    (fun p : ℂ × ℂ => selectedContinuedRoot p.1 p.2)
    (fun p hp => selectedContinuedRoot_joint_analyticAt (hKD hp).1 (hKD hp).2.1 (hKD hp).2.2) J
  obtain ⟨D,hD,hCoeff⟩ := compact_mixedRootCoefficients_finite_jets K hK (fun p hp => hKD hp) J
  refine ⟨max C D,lt_of_lt_of_le hC (le_max_left _ _),?_⟩
  intro f hp hm N eps τ lam θ i s hN heps hepsle hτ hl0 hl1 htl hθ hprof hs k hk
  have hpoint := hcover f hp hm N eps τ lam θ i s hN heps hepsle hτ hl0 hl1 htl hθ hprof hs
  exact ⟨(hRoot _ hpoint k hk).trans (le_max_left _ _),
    ((hCoeff _ hpoint k hk).1).trans (le_max_right _ _),
    ((hCoeff _ hpoint k hk).2).trans (le_max_right _ _)⟩


end
end IsingBulk.Tail
