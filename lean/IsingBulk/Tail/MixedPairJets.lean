import IsingBulk.Tail.MixedBranchIdentification
import IsingBulk.Tail.MixedCompactSourceSet
import IsingBulk.Tail.ProtectedCompletePairTransfer
import IsingBulk.Tail.CompactAnalyticJetBounds
import IsingBulk.Tail.MixedBranchChartNeighborhood
import IsingBulk.Tail.MixedCoarea

/-! Fixed-dimensional regular branch/compact complete-pair jets. The
compact tube is taken around all lower-quadrant branch phases, not only
phi=0, avoiding a circular branch-width/compact-gap choice. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter Metric
open scoped Topology BigOperators
attribute [local fun_prop] analyticAt_fst analyticAt_snd
set_option backward.isDefEq.respectTransparency false

def mixedBranchCompactPair (p : ℂ × ℂ × ℂ) : ℂ :=
  canceledPair (regularY p.1 p.2.1) p.2.2 (Complex.exp (-Complex.I*p.2.1))
    (selectedContinuedRoot p.1 p.2.2)

theorem mixedBranchCompactPair_analyticAt {s φ y : ℂ}
    (hs : s≠0) (hy : y≠0) (hW : sourceW s y∈continuedRootDomain)
    (hY : AnalyticAt ℂ (fun p : ℂ × ℂ => regularY p.1 p.2) (s,φ))
    (hgap : 1-Complex.exp (-Complex.I*φ)*selectedContinuedRoot s y≠0) :
    AnalyticAt ℂ mixedBranchCompactPair (s,φ,y) := by
  have ha : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => regularY p.1 p.2.1) (s,φ,y) := by
    exact AnalyticAt.comp_of_eq (g := fun p : ℂ × ℂ => regularY p.1 p.2)
      (f := fun p : ℂ × ℂ × ℂ => (p.1,p.2.1)) hY (by fun_prop) rfl
  have hz : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => selectedContinuedRoot p.1 p.2.2) (s,φ,y) := by
    exact AnalyticAt.comp_of_eq (g := fun p : ℂ × ℂ => selectedContinuedRoot p.1 p.2)
      (f := fun p : ℂ × ℂ × ℂ => (p.1,p.2.2))
      (selectedContinuedRoot_joint_analyticAt hs hy hW) (by fun_prop) rfl
  unfold mixedBranchCompactPair canceledPair
  apply AnalyticAt.div
  · fun_prop
  · fun_prop
  · exact mul_ne_zero (mul_ne_zero (regularY_ne_zero s φ) hy) (pow_ne_zero _ hgap)

def mixedLowerPhaseSet (r : ℝ) : Set ℂ :=
  closedBall 0 r ∩ {φ | 0≤φ.re ∧ φ.im≤0}

theorem mixedLowerPhaseSet_isCompact (r : ℝ) : IsCompact (mixedLowerPhaseSet r) :=
  (isCompact_closedBall _ _).inter_right
    ((isClosed_le continuous_const Complex.continuous_re).inter (isClosed_le Complex.continuous_im continuous_const))

theorem mixedLowerPhase_exp_lower_disk {r : ℝ} (hr : r≤Real.pi) {φ : ℂ}
    (hφ : φ∈mixedLowerPhaseSet r) :
    ‖Complex.exp (-Complex.I*φ)‖≤1 ∧ (Complex.exp (-Complex.I*φ)).im≤0 := by
  have hre : φ.re≤Real.pi :=
    (le_abs_self _).trans ((Complex.abs_re_le_norm φ).trans ((by simpa [mem_closedBall] using hφ.1 : ‖φ‖≤r).trans hr))
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hφ.2.1 hre
  constructor
  · rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simpa [Complex.mul_re] using hφ.2.2
  · rw [Complex.exp_im]
    have hi : (-Complex.I*φ).im= -φ.re := by simp [Complex.mul_im]
    rw [hi,Real.sin_neg]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (neg_nonpos.mpr hs)

/-- The tube surrounds every admissible branch phase in the fixed compact
quadrant. Compact roots cannot meet the reciprocal-root hypersurface. -/
theorem mixedBranchCompactPair_base_analytic {s : ℂ} {r : ℝ} (hr : r≤Real.pi)
    (hs : s≠0) {φ y : ℂ} (hφ : φ∈mixedLowerPhaseSet r)
    (hy : y≠0) (hW : sourceW s y∈continuedRootDomain)
    (hY : AnalyticAt ℂ (fun p : ℂ × ℂ => regularY p.1 p.2) (s,φ))
    (hz : ‖selectedContinuedRoot s y‖≤1) (hzi : (selectedContinuedRoot s y).im≤0) :
    AnalyticAt ℂ mixedBranchCompactPair (s,φ,y) := by
  have hends : selectedContinuedRoot s y≠1 ∧ selectedContinuedRoot s y≠ -1 := by
    constructor <;> intro he <;>
      have hh := continuedRoot_residue_gap hW <;>
      change 1-(selectedContinuedRoot s y)^2≠0 at hh <;> simp [he] at hh
  have hphase := mixedLowerPhase_exp_lower_disk hr hφ
  apply mixedBranchCompactPair_analyticAt hs hy hW hY
  simpa only [mul_comm] using lower_disk_pair_gap_of_not_endpoints hz hphase.1 hzi hphase.2 hends.1 hends.2

theorem mixed_base_compact_root_domain (d : LocalBranchData) {inner θ : ℝ}
    (hi : 0< inner) (hθ : inner/2≤|sectorDisplacement d.thetaB θ|) :
    sourceW (radialParameter d.theta 0) (limitingAngle θ)∈continuedRootDomain := by
  rw [sourceW_limitingAngle]
  have hlo := limitingAngularW_gt_neg_one d.a_pos θ
  have hne : limitingAngularW d.thetaB θ≠1 := by
    intro he
    have hz : sectorDisplacement d.thetaB θ=0 := by
      unfold limitingAngularW at he
      unfold sectorDisplacement
      linarith
    rw [hz,abs_zero] at hθ
    linarith
  by_cases hw : 1<limitingAngularW d.thetaB θ
  · exact Or.inl (Or.inr (by simpa using hw))
  · exact Or.inr (by simpa using abs_lt.mpr ⟨hlo,lt_of_le_of_ne (le_of_not_gt hw) hne⟩)

/-- Uniform finite jets on a genuine compact tube containing every fixed
quadrant branch phase and every limiting compact source coordinate. -/
theorem mixed_branch_compact_pair_tube (d : LocalBranchData) {r : ℝ}
    (hr : r≤Real.pi)
    (hY : ∀ φ∈mixedLowerPhaseSet r,AnalyticAt ℂ
      (fun p : ℂ × ℂ => regularY p.1 p.2) (radialParameter d.theta 0,φ))
    (inner : ℝ) (hi : 0< inner) (order : ℕ) :
    ∃ δ C : ℝ,0<δ ∧ 0<C ∧ ∀ φ∈mixedLowerPhaseSet r,
      ∀ θ∈Icc 0 (2*Real.pi),inner/2≤|sectorDisplacement d.thetaB θ| →
      ∀ p : ℂ × ℂ × ℂ,‖p-(radialParameter d.theta 0,φ,limitingAngle θ)‖≤δ →
      AnalyticAt ℂ mixedBranchCompactPair p ∧
      ∀ k≤order,‖iteratedFDeriv ℂ k mixedBranchCompactPair p‖≤C := by
  let A : Set ℝ := Icc 0 (2*Real.pi) ∩ {θ | inner/2≤|sectorDisplacement d.thetaB θ|}
  have hA : IsCompact A := isCompact_Icc.inter_right
    (isClosed_le continuous_const (by unfold sectorDisplacement; fun_prop))
  let F := fun p : ℂ × ℝ => (radialParameter d.theta 0,p.1,limitingAngle p.2)
  have hF : Continuous F := by unfold F limitingAngle; fun_prop
  let K := F '' (mixedLowerPhaseSet r ×ˢ A)
  have hK : IsCompact K := ((mixedLowerPhaseSet_isCompact r).prod hA).image hF
  have ha : AnalyticOnNhd ℂ mixedBranchCompactPair K := by
    rintro p ⟨⟨φ,θ⟩,⟨hφ,hθ⟩,rfl⟩
    have hs : radialParameter d.theta 0≠0 := norm_ne_zero_iff.mp (by
      rw [radialParameter_norm (by norm_num)]
      norm_num)
    have hy : limitingAngle θ≠0 := norm_ne_zero_iff.mp (by rw [limitingAngle_norm]; norm_num)
    have hd := mixed_base_compact_root_domain d hi hθ.2
    have hb := continuedRoot_real_lower_bounds (limitingAngularW_gt_neg_one d.a_pos θ)
    have he : selectedContinuedRoot (radialParameter d.theta 0) (limitingAngle θ)=
        continuedRoot (limitingAngularW d.thetaB θ) := by
      unfold selectedContinuedRoot
      rw [sourceW_limitingAngle]
    exact mixedBranchCompactPair_base_analytic hr hs hφ hy hd (hY φ hφ)
      (by simpa only [he] using hb.1) (by simpa only [he] using hb.2)
  obtain ⟨δ,C,hδ,hC,hjets⟩ := compact_analytic_jet_bounds mixedBranchCompactPair hK ha order
  obtain ⟨a,ha0,hA⟩ := hK.exists_cthickening_subset_open (isOpen_analyticAt ℂ mixedBranchCompactPair) ha
  refine ⟨min δ a,C,lt_min hδ ha0,hC,?_⟩
  intro φ hφ θ hθ hprofile p hp
  have hmem : (radialParameter d.theta 0,φ,limitingAngle θ)∈K :=
    ⟨(φ,θ),⟨hφ,hθ,hprofile⟩,rfl⟩
  refine ⟨hA (mem_cthickening_of_dist_le p _ a K hmem (by
    simpa only [dist_eq_norm] using hp.trans (min_le_right _ _))),?_⟩
  intro k hk
  exact (hjets _ hmem p (hp.trans (min_le_left _ _)) k hk).1

theorem mixed_regular_phase_radius (d : LocalBranchData) :
    ∃ r : ℝ,0<r ∧ r≤Real.pi ∧ ∀ φ∈mixedLowerPhaseSet r,
      AnalyticAt ℂ (fun p : ℂ × ℂ => regularY p.1 p.2) (radialParameter d.theta 0,φ) := by
  let s₀ := radialParameter d.theta 0
  have hs : s₀≠0 := norm_ne_zero_iff.mp (by
    change ‖radialParameter d.theta 0‖≠0
    rw [radialParameter_norm (by norm_num)]
    norm_num)
  have hS : s₀+s₀⁻¹=(1+(Real.cos d.thetaB:ℂ)) := by
    simpa [s₀,IsingBulk.First.sourceS] using sourceS_radial_zero_branch d
  have hc : |Real.cos d.thetaB|<1 := by
    have hsin : 0<Real.sin d.thetaB := d.a_pos
    rw [abs_lt]
    constructor <;> nlinarith [hsin,Real.sin_sq_add_cos_sq d.thetaB,
      Real.cos_le_one d.thetaB,Real.neg_one_le_cos d.thetaB]
  have ha := regularY_analytic_base s₀ (Real.cos d.thetaB) hs hS hc
  have he : ∀ᶠ p in 𝓝 (s₀,(0:ℂ)),AnalyticAt ℂ (fun p : ℂ × ℂ => regularY p.1 p.2) p :=
    (isOpen_analyticAt ℂ (fun p : ℂ × ℂ => regularY p.1 p.2)).mem_nhds ha
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min (δ/2) 1,lt_min (by positivity) zero_lt_one,
    (min_le_right _ _).trans (by linarith [Real.pi_gt_three]),?_⟩
  intro φ hφ
  apply hball
  change dist (s₀,φ) (s₀,(0:ℂ))<δ
  rw [Prod.dist_eq]
  have hn : ‖φ‖≤min (δ/2) 1 := by simpa [mem_closedBall] using hφ.1
  simp only [dist_self,dist_zero_right,max_eq_right (norm_nonneg φ)]
  exact (hn.trans (min_le_left _ _)).trans_lt (half_lt_self hδ)

theorem mixed_actual_pair_tube_motion (d : LocalBranchData) {δ : ℝ} (hδ : 0<δ) :
    ∃ e t₀ : ℝ,0<e ∧ 0<t₀ ∧ ∀ (f : SelectorFunctions),
      (∀ x,0≤f.p x ∧ f.p x≤1) → (∀ x,0≤f.m x ∧ f.m x≤1) →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) (s : ℂ),
      1≤N → 0≤eps → eps≤e → 0≤τ → 0≤lam → lam≤1 → lam*τ≤t₀ →
      ‖s-radialParameter d.theta eps‖≤(1/4:ℝ)*eps →
      ‖s-radialParameter d.theta 0‖≤δ ∧
      ‖deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i-limitingAngle (θ i)‖≤δ := by
  let e := min 1 (min (1/(4*(d.c₀+1))) (δ/(8*(d.c₀+1))))
  let t₀ := min (1/8:ℝ) (δ/16)
  have he : 0<e := by dsimp [e]; positivity [d.c₀_pos]
  have ht : 0<t₀ := by dsimp [t₀]; positivity
  refine ⟨e,t₀,he,ht,?_⟩
  intro f hp hm N eps τ lam θ i s hN heps hepsle hτ hl0 _hl1 htl hs
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have heb := hepsle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hed := hepsle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hb := (le_div_iff₀ (by positivity [d.c₀_pos] : 0<4*(d.c₀+1))).mp heb
  have hd := (le_div_iff₀ (by positivity [d.c₀_pos] : 0<8*(d.c₀+1))).mp hed
  have hτe : lam*τ≤1/8 := htl.trans (min_le_left _ _)
  have hτδ : lam*τ≤δ/16 := htl.trans (min_le_right _ _)
  let v := coupledRadialExponent d.c₀ eps (lam*τ) 1 (f.p (θ i)) (f.m (θ i))
    (occupancy (fun j => f.p (θ j))/(N:ℝ))
  have hvb : |v|≤d.c₀*eps+2*(lam*τ) := coupledRadialExponent_bound d.c₀_pos.le heps
    (mul_nonneg hl0 hτ) (by norm_num) (by norm_num) (hp _).1 (hp _).2 (hm _).1 (hm _).2
    (div_nonneg (occupancy_nonneg (fun j => (hp (θ j)).1)) hn.le)
    ((div_le_one hn).mpr (occupancy_le (fun j => (hp (θ j)).2)))
  have hv : |v|≤1 := hvb.trans (by nlinarith)
  constructor
  · have hh := norm_sub_le_norm_sub_add_norm_sub s (radialParameter d.theta eps) (radialParameter d.theta 0)
    rw [radialParameter_sub_zero_norm d.theta eps heps] at hh
    nlinarith [mul_nonneg d.c₀_pos.le heps]
  · have hy : deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i=radialAnglePoint v (θ i) := by
      rw [deformedPoint_scale_lambda,deformedPoint_coupledRadialExponent]
    rw [hy]
    exact (radialAnglePoint_motion hv _).trans (by nlinarith [mul_nonneg d.c₀_pos.le heps])

/-- Actual full-occupancy branch/compact scalar jets on the original disk.
The branch width is chosen before the compact-pair tube, whose constants
may then depend on that fixed width but never on particle number. -/
theorem mixed_actual_branch_compact_pair_jets_below_cap (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) (order : ℕ) :
    ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ inner : ℝ,0< inner → inner≤ inner₀ →
      ∃ c e t₀ C : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ 0<C ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (j k : Fin N) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
      |sectorDisplacement d.thetaB (θ j)|≤ inner →
      θ k∈Icc 0 (2*Real.pi) → inner/2≤|sectorDisplacement d.thetaB (θ k)| →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
      AnalyticAt ℂ mixedBranchCompactPair (s,mixedSourcePhase s (y j),y k) ∧
      ∀ l≤order,‖iteratedFDeriv ℂ l mixedBranchCompactPair (s,mixedSourcePhase s (y j),y k)‖≤C := by
  obtain ⟨r,hr,hrpi,hY⟩ := mixed_regular_phase_radius d
  let U : Set (ℂ × ℂ) := {p | ‖p.2‖<r}
  have hU : IsOpen U := isOpen_lt (continuous_snd.norm) continuous_const
  have hbase : (radialParameter d.theta 0,(0:ℂ))∈U := by simpa [U] using hr
  obtain ⟨inner₀,cB,eB,tB,hi₀,hicap,hcB,heB,htB,hBranch⟩ :=
    mixed_actual_branch_chart_neighborhood d hcsmall U hU hbase cap hcap
  refine ⟨inner₀,hi₀,hicap,?_⟩
  intro inner hi hinner
  obtain ⟨δ,C,hδ,hC,hPair⟩ := mixed_branch_compact_pair_tube d hrpi hY inner hi order
  obtain ⟨eM,tM,heM,htM,hMotion⟩ := mixed_actual_pair_tube_motion d hδ
  obtain ⟨cG,eG,tG,hcG,heG,htG,hGeometry⟩ := mixed_actual_uniform_source_data d hcsmall 1 zero_lt_one
  refine ⟨min cB (min cG (1/4)),min eB (min eG eM),min tB (min tG tM),C,
    lt_min hcB (lt_min hcG (by norm_num)),lt_min heB (lt_min heG heM),
    lt_min htB (lt_min htG htM),hC,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ j k s hN heps hepslt hτ hl0 hl1 htl hBranchProfile hθk hCompactProfile hs
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  let φ := mixedSourcePhase s (y j)
  have hsB := hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le)
  have hsG := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) heps.le)
  have hsM := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) heps.le)
  have hphaseNorm : ‖φ‖≤r := (hBranch η α hη hηsmall hα N eps τ lam θ j s hN heps
    (hepslt.trans_le (min_le_left _ _)) hτ hl0 hl1 (htl.trans_le (min_le_left _ _)) (hBranchProfile.trans hinner) hsB).le
  obtain ⟨_,hGeo⟩ := hGeometry η α hη hηsmall hα N eps τ lam θ s hN heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hτ hl0 hl1
    (htl.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hsG
  obtain ⟨v,hv,hy,hclose,hW⟩ := hGeo j
  have hquad := mixedSourcePhase_upper_bounds hW
  have hφ : φ∈mixedLowerPhaseSet r := ⟨by simpa [mem_closedBall] using hphaseNorm,hquad.1.le,hquad.2.2.le⟩
  have hm := hMotion f (fun x => thresholdStep_range _ _ _)
    (fun x => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
    N eps τ lam θ k s hN heps.le
    (hepslt.le.trans ((min_le_right _ _).trans (min_le_right _ _))) hτ hl0 hl1
    (htl.le.trans ((min_le_right _ _).trans (min_le_right _ _))) hsM
  apply hPair φ hφ (θ k) hθk hCompactProfile (s,φ,y k)
  change max ‖s-radialParameter d.theta 0‖ (max ‖φ-φ‖ ‖y k-limitingAngle (θ k)‖)≤δ
  simp only [sub_self,norm_zero,max_eq_right (norm_nonneg _)]
  exact max_le hm.1 hm.2

end
end IsingBulk.Tail
