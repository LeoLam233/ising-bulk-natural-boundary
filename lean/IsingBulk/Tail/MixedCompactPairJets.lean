import IsingBulk.Tail.MixedPairJets

/-! Compact--compact literal canceled-pair jets in joint (s,y_i,y_j)
coordinates. Both compact source coordinates move, including spectators. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric
open scoped Topology
attribute [local fun_prop] analyticAt_fst analyticAt_snd
set_option backward.isDefEq.respectTransparency false

def mixedCompactPair (p : ℂ × ℂ × ℂ) : ℂ :=
  canceledPair p.2.1 p.2.2 (selectedContinuedRoot p.1 p.2.1) (selectedContinuedRoot p.1 p.2.2)

theorem mixedCompactPair_analyticAt {s y v : ℂ}
    (hs : s≠0) (hy : y≠0) (hv : v≠0)
    (hWy : sourceW s y∈continuedRootDomain) (hWv : sourceW s v∈continuedRootDomain)
    (hgap : 1-selectedContinuedRoot s y*selectedContinuedRoot s v≠0) :
    AnalyticAt ℂ mixedCompactPair (s,y,v) := by
  have hzy : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => selectedContinuedRoot p.1 p.2.1) (s,y,v) :=
    AnalyticAt.comp_of_eq (g := fun p : ℂ × ℂ => selectedContinuedRoot p.1 p.2)
      (f := fun p : ℂ × ℂ × ℂ => (p.1,p.2.1))
      (selectedContinuedRoot_joint_analyticAt hs hy hWy) (by fun_prop) rfl
  have hzv : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => selectedContinuedRoot p.1 p.2.2) (s,y,v) :=
    AnalyticAt.comp_of_eq (g := fun p : ℂ × ℂ => selectedContinuedRoot p.1 p.2)
      (f := fun p : ℂ × ℂ × ℂ => (p.1,p.2.2))
      (selectedContinuedRoot_joint_analyticAt hs hv hWv) (by fun_prop) rfl
  unfold mixedCompactPair canceledPair
  apply AnalyticAt.div
  · fun_prop
  · fun_prop
  · exact mul_ne_zero (mul_ne_zero hy hv) (pow_ne_zero _ hgap)

theorem mixedCompactPair_base_analytic (d : LocalBranchData) {inner θ φ : ℝ}
    (hi : 0< inner) (hθ : inner/2≤|sectorDisplacement d.thetaB θ|)
    (hφ : inner/2≤|sectorDisplacement d.thetaB φ|) :
    AnalyticAt ℂ mixedCompactPair (radialParameter d.theta 0,limitingAngle θ,limitingAngle φ) := by
  have hs : radialParameter d.theta 0≠0 := norm_ne_zero_iff.mp (by
    rw [radialParameter_norm (by norm_num)]
    norm_num)
  have hy (t : ℝ) : limitingAngle t≠0 := norm_ne_zero_iff.mp (by rw [limitingAngle_norm]; norm_num)
  have hDθ := mixed_base_compact_root_domain d hi hθ
  have hDφ := mixed_base_compact_root_domain d hi hφ
  have hbounds (t : ℝ) : ‖selectedContinuedRoot (radialParameter d.theta 0) (limitingAngle t)‖≤1 ∧
      (selectedContinuedRoot (radialParameter d.theta 0) (limitingAngle t)).im≤0 := by
    have hh := continuedRoot_real_lower_bounds (limitingAngularW_gt_neg_one d.a_pos t)
    simpa only [selectedContinuedRoot,sourceW_limitingAngle] using hh
  have hends : selectedContinuedRoot (radialParameter d.theta 0) (limitingAngle θ)≠1 ∧
      selectedContinuedRoot (radialParameter d.theta 0) (limitingAngle θ)≠ -1 := by
    constructor <;> intro he <;> have hh := continuedRoot_residue_gap hDθ <;>
      change 1-(selectedContinuedRoot (radialParameter d.theta 0) (limitingAngle θ))^2≠0 at hh <;>
      simp [he] at hh
  exact mixedCompactPair_analyticAt hs (hy θ) (hy φ) hDθ hDφ
    (lower_disk_pair_gap_of_not_endpoints (hbounds θ).1 (hbounds φ).1 (hbounds θ).2 (hbounds φ).2 hends.1 hends.2)

theorem mixed_compact_pair_tube (d : LocalBranchData) (inner : ℝ) (hi : 0< inner) (order : ℕ) :
    ∃ δ C : ℝ,0<δ ∧ 0<C ∧ ∀ θ∈Icc 0 (2*Real.pi),∀ φ∈Icc 0 (2*Real.pi),
      inner/2≤|sectorDisplacement d.thetaB θ| → inner/2≤|sectorDisplacement d.thetaB φ| →
      ∀ p : ℂ × ℂ × ℂ,‖p-(radialParameter d.theta 0,limitingAngle θ,limitingAngle φ)‖≤δ →
      AnalyticAt ℂ mixedCompactPair p ∧ ∀ k≤order,‖iteratedFDeriv ℂ k mixedCompactPair p‖≤C := by
  let A : Set ℝ := Icc 0 (2*Real.pi) ∩ {θ | inner/2≤|sectorDisplacement d.thetaB θ|}
  have hA : IsCompact A := isCompact_Icc.inter_right
    (isClosed_le continuous_const (by unfold sectorDisplacement; fun_prop))
  let F := fun p : ℝ × ℝ => (radialParameter d.theta 0,limitingAngle p.1,limitingAngle p.2)
  have hF : Continuous F := by unfold F limitingAngle; fun_prop
  let K := F '' (A ×ˢ A)
  have hK : IsCompact K := (hA.prod hA).image hF
  have ha : AnalyticOnNhd ℂ mixedCompactPair K := by
    rintro p ⟨⟨θ,φ⟩,⟨hθ,hφ⟩,rfl⟩
    exact mixedCompactPair_base_analytic d hi hθ.2 hφ.2
  obtain ⟨δ,C,hδ,hC,hjets⟩ := compact_analytic_jet_bounds mixedCompactPair hK ha order
  obtain ⟨r,hr,hrsub⟩ := hK.exists_cthickening_subset_open (isOpen_analyticAt ℂ mixedCompactPair) ha
  refine ⟨min δ r,C,lt_min hδ hr,hC,?_⟩
  intro θ hθ φ hφ hθp hφp p hp
  have hbase : (radialParameter d.theta 0,limitingAngle θ,limitingAngle φ)∈K :=
    ⟨(θ,φ),⟨⟨hθ,hθp⟩,⟨hφ,hφp⟩⟩,rfl⟩
  refine ⟨hrsub (mem_cthickening_of_dist_le p _ r K hbase ?_),?_⟩
  · simpa only [dist_eq_norm] using hp.trans (min_le_right δ r)
  · intro k hk
    exact (hjets _ hbase p (hp.trans (min_le_left δ r)) k hk).1


theorem mixed_actual_compact_pair_jets (d : LocalBranchData) (inner : ℝ) (hi : 0< inner) (order : ℕ) :
    ∃ e t₀ C : ℝ,0<e ∧ 0<t₀ ∧ 0<C ∧ ∀ (f : SelectorFunctions),
      (∀ x,0≤f.p x ∧ f.p x≤1) → (∀ x,0≤f.m x ∧ f.m x≤1) →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (i j : Fin N) (s : ℂ),
      1≤N → 0≤eps → eps≤e → 0≤τ → 0≤lam → lam≤1 → lam*τ≤t₀ → θ∈angleBox N →
      inner/2≤|sectorDisplacement d.thetaB (θ i)| → inner/2≤|sectorDisplacement d.thetaB (θ j)| →
      ‖s-radialParameter d.theta eps‖≤(1/4:ℝ)*eps →
      AnalyticAt ℂ mixedCompactPair (s,deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i,
        deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ j) ∧ ∀ k≤order,
      ‖iteratedFDeriv ℂ k mixedCompactPair
        (s,deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i,
          deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ j)‖≤C := by
  obtain ⟨δ,C,hδ,hC,hTube⟩ := mixed_compact_pair_tube d inner hi order
  obtain ⟨e,t₀,he,ht,hMotion⟩ := mixed_actual_pair_tube_motion d hδ
  refine ⟨e,t₀,C,he,ht,hC,?_⟩
  intro f hp hm N eps τ lam θ i j s hN heps hepsle hτ hl0 hl1 htl hθ hiP hjP hs
  have hiM := hMotion f hp hm N eps τ lam θ i s hN heps hepsle hτ hl0 hl1 htl hs
  have hjM := hMotion f hp hm N eps τ lam θ j s hN heps hepsle hτ hl0 hl1 htl hs
  apply hTube (θ i) ⟨hθ.1 i,hθ.2 i⟩ (θ j) ⟨hθ.1 j,hθ.2 j⟩ hiP hjP _ ?_
  change ‖(s-radialParameter d.theta 0,
    deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ i-limitingAngle (θ i),
    deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ j-limitingAngle (θ j))‖≤δ
  simpa only [Prod.norm_def] using max_le hiM.1 (max_le hiM.2 hjM.2)

end
end IsingBulk.Tail
