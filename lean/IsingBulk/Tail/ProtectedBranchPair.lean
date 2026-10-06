import IsingBulk.Tail.ProtectedBranchDisk
import IsingBulk.Tail.SchurContraction
import IsingBulk.Tail.SelectedFContinuation

/-! Strict complete B-by-B contraction from the actual y-pair near the
single lower branch point and physical-sheet z contraction. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Filter Metric
open scoped Topology

theorem same_point_pair_strict_neighborhood (y₀ : ℂ) (hy₀ : 1-y₀*y₀ ≠ 0)
    {q : ℝ} (hq : 0<q) :
    ∃ r : ℝ, 0<r ∧ ∀ y v : ℂ, ‖y-y₀‖<r → ‖v-y₀‖<r → 1-y*v ≠ 0 ∧ ‖pairKernel y v‖<q := by
  have hc : ContinuousAt (fun p : ℂ × ℂ => pairKernel p.1 p.2) (y₀,y₀) := by
    unfold pairKernel
    exact (continuousAt_fst.sub continuousAt_snd).div
      (continuousAt_const.sub (continuousAt_fst.mul continuousAt_snd)) hy₀
  have hz : ‖pairKernel y₀ y₀‖<q := by simpa [pairKernel] using hq
  have hd : ContinuousAt (fun p : ℂ × ℂ => 1-p.1*p.2) (y₀,y₀) := by fun_prop
  obtain ⟨r,hr,hbound⟩ := Metric.eventually_nhds_iff.mp
    ((hd.eventually_ne hy₀).and (hc.norm.eventually_lt continuousAt_const hz))
  refine ⟨r,hr,?_⟩
  intro y v hy hv
  exact hbound (y := (y,v)) (by simpa [Prod.dist_eq,max_lt_iff,dist_eq_norm] using And.intro hy hv)

theorem lower_branch_y_pair_strict (d : LocalBranchData) {q : ℝ} (hq : 0<q) :
    ∃ r : ℝ, 0<r ∧ ∀ eps v u w : ℝ,
      |eps|<r → |v|<r → |u|<r → |w|<r →
      (1-plateauY d.c₀ eps 1 v d.thetaB u*plateauY d.c₀ eps 1 v d.thetaB w ≠ 0) ∧
      ‖pairKernel (plateauY d.c₀ eps 1 v d.thetaB u)
        (plateauY d.c₀ eps 1 v d.thetaB w)‖<q := by
  let y₀ := Complex.exp ((-d.thetaB:ℝ)*Complex.I)
  have hyim : y₀.im = -Real.sin d.thetaB := by
    simp only [y₀,Complex.exp_ofReal_mul_I_im,Real.sin_neg]
  have hsin : 0<Real.sin d.thetaB := d.a_pos
  have hy0 : 1-y₀*y₀ ≠ 0 := by
    intro h
    have hsq : y₀^2=1 := by linear_combination -h
    rcases (sq_eq_one_iff.mp hsq) with hp|hm
    · have hi := congrArg Complex.im hp
      simp only [Complex.one_im] at hi
      linarith
    · have hi := congrArg Complex.im hm
      norm_num at hi
      linarith
  obtain ⟨r,hr,hpair⟩ := same_point_pair_strict_neighborhood y₀ hy0 hq
  have hc : ContinuousAt (fun p : ℝ × ℝ × ℝ => plateauY d.c₀ p.1 1 p.2.1 d.thetaB p.2.2) 0 := by
    unfold plateauY
    fun_prop
  have he : plateauY d.c₀ 0 1 0 d.thetaB 0=y₀ := by simp [plateauY,y₀]
  obtain ⟨a,ha,hnear⟩ := Metric.eventually_nhds_iff.mp
    ((hc.sub continuousAt_const).norm.eventually_lt continuousAt_const
      (show ‖plateauY d.c₀ 0 1 0 d.thetaB 0-y₀‖<r by rw [he,sub_self,norm_zero]; exact hr))
  refine ⟨a,ha,?_⟩
  intro eps v u w heps hv hu hw
  apply hpair
  · apply hnear (y := (eps,v,u))
    simpa [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using And.intro heps (And.intro hv hu)
  · apply hnear (y := (eps,v,w))
    simpa [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using And.intro heps (And.intro hv hw)


/-- Uniform strictness for the literal complete canceled lower-branch pair
on every protected disk. No inverse power of lambda enters this constant. -/
theorem protected_lower_branch_complete_pair (d : LocalBranchData) {q : ℝ} (hq : 0<q) :
    ∃ r : ℝ, 0<r ∧ ∀ τ : ℝ, 0<τ → τ<r → ∃ c : ℝ, 0<c ∧
      ∀ (N : ℕ) (eps lamStar lam P u w : ℝ) (s : ℂ),
        1≤N → 0<eps → eps<r → 0<lamStar → lamStar≤lam → lam≤1 →
        1≤P → P≤N → |u|<r → |w|<r →
        ‖s-radialParameter d.theta eps‖ ≤ c*lamStar/(N:ℝ)^2 →
        let y := plateauY d.c₀ eps τ (lam*P/(N:ℝ)) d.thetaB u
        let v := plateauY d.c₀ eps τ (lam*P/(N:ℝ)) d.thetaB w
        ‖canceledPair y v (selectedContinuedRoot s y) (selectedContinuedRoot s v)‖<q := by
  obtain ⟨ry,hry,hy⟩ := lower_branch_y_pair_strict d hq
  obtain ⟨b,rb,hb,hrb,hbranch⟩ := protected_disk_true_branch d
  refine ⟨min ry rb,lt_min hry hrb,?_⟩
  intro τ hτ hτr
  obtain ⟨c,hc,hB⟩ := hbranch τ hτ (hτr.trans_le (min_le_right _ _))
  refine ⟨c,hc,?_⟩
  intro N eps lamStar lam P u w s hN heps hepsr hls hl hl1 hP hPN hu hw hsd
  let t := lam*P/(N:ℝ)
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlam : 0≤lam := hls.le.trans hl
  have ht : 0≤t := by dsimp [t]; positivity
  have ht1 : t≤1 := by
    apply (div_le_one hn).mpr
    nlinarith
  have hv : |τ*t|<ry := by
    rw [abs_of_nonneg (mul_nonneg hτ.le ht)]
    exact (mul_le_of_le_one_right hτ.le ht1).trans_lt (hτr.trans_le (min_le_left _ _))
  have hyeq (a : ℝ) : plateauY d.c₀ eps 1 (τ*t) d.thetaB a=
      plateauY d.c₀ eps τ t d.thetaB a := by simp [plateauY]
  obtain ⟨hygap,hypair⟩ := hy eps (τ*t) u w
    (by simpa [abs_of_pos heps] using hepsr.trans_le (min_le_left _ _)) hv
    (hu.trans_le (min_le_left _ _)) (hw.trans_le (min_le_left _ _))
  rw [hyeq u,hyeq w] at hygap hypair
  have hpos (a : ℝ) (ha : |a|<rb) :
      0<(sourceW s (plateauY d.c₀ eps τ t d.thetaB a)).im := by
    have hh := (hB N eps lamStar lam P a s hN heps
      (hepsr.trans_le (min_le_right _ _)) hls hl hl1 hP hPN ha hsd).1
    have hp : 0<b*(eps+τ*t) := by positivity
    exact hp.trans_le hh
  let y := plateauY d.c₀ eps τ t d.thetaB u
  let v := plateauY d.c₀ eps τ t d.thetaB w
  let z := selectedContinuedRoot s y
  let z' := selectedContinuedRoot s v
  have hyW := hpos u (hu.trans_le (min_le_right _ _))
  have hvW := hpos w (hw.trans_le (min_le_right _ _))
  have hz : z=interiorRoot (sourceW s y) := continuedRoot_eq_interiorRoot hyW
  have hz' : z'=interiorRoot (sourceW s v) := continuedRoot_eq_interiorRoot hvW
  have hzn : ‖z‖≤1 := by rw [hz]; exact (interiorRoot_norm_lt_one hyW).le
  have hz'n : ‖z'‖≤1 := by rw [hz']; exact (interiorRoot_norm_lt_one hvW).le
  have hzi : z.im≤0 := by rw [hz]; exact (interiorRoot_lower_im hyW).le
  have hz'i : z'.im≤0 := by rw [hz']; exact (interiorRoot_lower_im hvW).le
  have hp : ‖pairKernel z z'‖≤1 := schur_norm_le hzn hz'n (mul_nonneg_of_nonpos_of_nonpos hzi hz'i)
  have hquad (a : ℂ) : (selectedContinuedRoot s a)^2-(2*sourceS s-a-a⁻¹)*selectedContinuedRoot s a+1=0 := by
    have hh := continuedRoot_quadratic (sourceW s a)
    dsimp [selectedContinuedRoot,sourceW] at hh ⊢
    linear_combination hh
  have hident := source_pair_identity (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    (continuedRoot_nonzero _) (continuedRoot_nonzero _) (hquad y) (hquad v) hygap
    (continuedRoot_pair_gap (Or.inl (Or.inl hyW)) (Or.inl (Or.inl hvW)))
  change ‖canceledPair y v z z'‖<q
  change pairKernel z z'*pairKernel y v=canceledPair y v z z' at hident
  rw [← hident,norm_mul]
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_lt (by simpa using hypair)

end
end IsingBulk.Tail
