import IsingBulk.Tail.ClosedUpperRootBoundary
import IsingBulk.Tail.CompactPairGap
import IsingBulk.Tail.SelectorCutoffs
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Uniform transfer of complete canceled pairs from the closed lower-circle
limiting geometry. Positive endpoint slivers are reflected before transfer. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology

def lowerCircleProjection (θ : ℝ) : ℂ := (Real.cos θ:ℂ)-Complex.I*((|Real.sin θ|:ℝ):ℂ)
def reflectedLowerChord (b θ : ℝ) : ℝ :=
  (Real.cos θ-Real.cos b)^2+(|Real.sin θ|-Real.sin b)^2

def lowerProjectedRoot (b θ : ℝ) : ℂ := continuedRoot (limitingAngularW b θ:ℂ)

def lowerProjectedPair (b : ℝ) (p : ℝ × ℝ) : ℂ :=
  canceledPair (lowerCircleProjection p.1) (lowerCircleProjection p.2)
    (lowerProjectedRoot b p.1) (lowerProjectedRoot b p.2)

theorem lowerCircleProjection_continuous : Continuous lowerCircleProjection := by
  unfold lowerCircleProjection
  fun_prop

theorem lowerCircleProjection_re (θ : ℝ) : (lowerCircleProjection θ).re=Real.cos θ := by
  simp only [lowerCircleProjection,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_zero]

theorem lowerCircleProjection_im (θ : ℝ) : (lowerCircleProjection θ).im= -|Real.sin θ| := by
  simp [lowerCircleProjection]

theorem lowerCircleProjection_norm (θ : ℝ) : ‖lowerCircleProjection θ‖=1 := by
  have h := Real.sin_sq_add_cos_sq θ
  have he : Complex.normSq (lowerCircleProjection θ)=1 := by
    rw [Complex.normSq_apply,lowerCircleProjection_re,lowerCircleProjection_im]
    nlinarith [sq_abs (Real.sin θ)]
  rw [← Complex.sq_norm] at he
  nlinarith [norm_nonneg (lowerCircleProjection θ)]

theorem lowerCircleProjection_trace (θ : ℝ) :
    lowerCircleProjection θ+(lowerCircleProjection θ)⁻¹=2*(Real.cos θ:ℂ) := by
  rw [Complex.inv_eq_conj (lowerCircleProjection_norm θ)]
  rw [Complex.add_conj,lowerCircleProjection_re]
  push_cast
  rfl

theorem limitingAngularW_gt_neg_one {b : ℝ} (hb : 0 < Real.sin b) (θ : ℝ) :
    -1 < limitingAngularW b θ := by
  have hc : -1 < Real.cos b := by
    have h := Real.sin_sq_add_cos_sq b
    nlinarith [Real.neg_one_le_cos b,Real.cos_le_one b,sq_pos_of_pos hb]
  unfold limitingAngularW
  linarith [Real.cos_le_one θ]

theorem lowerProjectedRoot_continuous {b : ℝ} (hb : 0 < Real.sin b) :
    Continuous (lowerProjectedRoot b) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  exact (continuedRoot_continuousAt_real (limitingAngularW_gt_neg_one hb θ)).comp
    (f := fun t : ℝ => (limitingAngularW b t:ℂ)) (by unfold limitingAngularW; fun_prop)

theorem reflectedLowerChord_zero_of_branch {b θ : ℝ} (hb : 0 < Real.sin b)
    (hW : limitingAngularW b θ=1) : reflectedLowerChord b θ=0 := by
  have hc : Real.cos θ=Real.cos b := by unfold limitingAngularW at hW; linarith
  have hs : |Real.sin θ|=Real.sin b := by
    have h₁ := Real.sin_sq_add_cos_sq θ
    have h₂ := Real.sin_sq_add_cos_sq b
    rw [hc] at h₁
    nlinarith [sq_abs (Real.sin θ),abs_nonneg (Real.sin θ)]
  simp [reflectedLowerChord,hc,hs]

theorem lowerProjectedRoot_quadratic (s : ℂ) (b θ : ℝ)
    (hS : sourceS s=((1+Real.cos b:ℝ):ℂ)) :
    (lowerProjectedRoot b θ)^2-(2*sourceS s-lowerCircleProjection θ-(lowerCircleProjection θ)⁻¹)*
      lowerProjectedRoot b θ+1=0 := by
  have ht := lowerCircleProjection_trace θ
  have he : 2*sourceS s-lowerCircleProjection θ-(lowerCircleProjection θ)⁻¹ =
      2*(limitingAngularW b θ:ℂ) := by
    rw [hS]
    unfold limitingAngularW
    push_cast at ht ⊢
    linear_combination -ht
  rw [he]
  exact continuedRoot_quadratic _

theorem lower_disk_pair_gap_of_not_endpoints {z w : ℂ}
    (hz : ‖z‖≤1) (hw : ‖w‖≤1) (hzi : z.im≤0) (hwi : w.im≤0)
    (hz1 : z≠1) (hzm : z≠ -1) : 1-z*w≠0 := by
  rcases lower_disk_strict_alternative hz hzi hz1 hzm with hn | hi
  · apply norm_pos_iff.mp
    have hg := compact_norm_denominator_gap (z := z) (w := w) (d := 1-‖z‖) (by linarith) hw
    linarith
  · apply norm_pos_iff.mp
    have hg := compact_imaginary_denominator_gap (d := -z.im) (by linarith) hz (by linarith) hwi
    linarith

theorem lowerProjectedPair_gap {b θ φ h : ℝ} (hb : 0 < Real.sin b) (hh : 0 < h)
    (hc : h ≤ reflectedLowerChord b θ ∨ h ≤ reflectedLowerChord b φ) :
    1-lowerProjectedRoot b θ*lowerProjectedRoot b φ≠0 := by
  have hθ := continuedRoot_real_lower_bounds (limitingAngularW_gt_neg_one hb θ)
  have hφ := continuedRoot_real_lower_bounds (limitingAngularW_gt_neg_one hb φ)
  have hne (t : ℝ) (ht : h ≤ reflectedLowerChord b t) : lowerProjectedRoot b t≠1 := by
    apply continuedRoot_real_ne_one
    intro he
    rw [reflectedLowerChord_zero_of_branch hb he] at ht
    linarith
  rcases hc with hc | hc
  · exact lower_disk_pair_gap_of_not_endpoints hθ.1 hφ.1 hθ.2 hφ.2 (hne θ hc)
      (continuedRoot_real_ne_neg_one (limitingAngularW_gt_neg_one hb θ))
  · simpa only [lowerProjectedRoot,mul_comm] using lower_disk_pair_gap_of_not_endpoints hφ.1 hθ.1 hφ.2 hθ.2 (hne φ hc)
      (continuedRoot_real_ne_neg_one (limitingAngularW_gt_neg_one hb φ))

theorem complete_pair_le_one_lower {a b z w s : ℂ}
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hai : a.im≤0) (hbi : b.im≤0)
    (hz0 : z≠0) (hw0 : w≠0) (hz : ‖z‖≤1) (hw : ‖w‖≤1) (hzi : z.im≤0) (hwi : w.im≤0)
    (hzq : z^2-(2*sourceS s-a-a⁻¹)*z+1=0)
    (hwq : w^2-(2*sourceS s-b-b⁻¹)*w+1=0) (hzw : 1-z*w≠0) :
    ‖canceledPair a b z w‖ ≤ 1 := by
  by_cases hab : 1-a*b=0
  · have he := lower_unit_reciprocal_eq ha hai hbi hab
    simp [canceledPair,he]
  · have ha0 : a≠0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
    have hb0 : b≠0 := norm_ne_zero_iff.mp (by rw [hb]; norm_num)
    have he := source_pair_identity ha0 hb0 hz0 hw0 hzq hwq hab hzw
    change ‖-(a-b)^2*z*w/(a*b*(1-z*w)^2)‖ ≤ 1
    rw [← he,norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (schur_norm_le ha.le hb.le
      (mul_nonneg_of_nonpos_of_nonpos hai hbi))).trans
      (schur_norm_le hz hw (mul_nonneg_of_nonpos_of_nonpos hzi hwi))

theorem lowerProjectedPair_le_one (s : ℂ) {b θ φ h : ℝ}
    (hS : sourceS s=((1+Real.cos b:ℝ):ℂ)) (hb : 0<Real.sin b) (hh : 0<h)
    (hc : h≤reflectedLowerChord b θ ∨ h≤reflectedLowerChord b φ) :
    ‖lowerProjectedPair b (θ,φ)‖ ≤ 1 := by
  obtain ⟨hθn,hθi⟩ := continuedRoot_real_lower_bounds (limitingAngularW_gt_neg_one hb θ)
  obtain ⟨hφn,hφi⟩ := continuedRoot_real_lower_bounds (limitingAngularW_gt_neg_one hb φ)
  apply complete_pair_le_one_lower (s := s) (lowerCircleProjection_norm θ) (lowerCircleProjection_norm φ)
    (by rw [lowerCircleProjection_im]; exact neg_nonpos.mpr (abs_nonneg _))
    (by rw [lowerCircleProjection_im]; exact neg_nonpos.mpr (abs_nonneg _))
    (continuedRoot_nonzero _) (continuedRoot_nonzero _) hθn hφn hθi hφi
    (lowerProjectedRoot_quadratic s b θ hS) (lowerProjectedRoot_quadratic s b φ hS)
    (lowerProjectedPair_gap hb hh hc)

theorem lowerProjectedPair_same_strict (s : ℂ) {b θ φ h : ℝ}
    (hS : sourceS s=((1+Real.cos b:ℝ):ℂ)) (hb : 0<Real.sin b) (hh : 0<h)
    (hθ : h≤reflectedLowerChord b θ) (hφ : h≤reflectedLowerChord b φ)
    (hcolor : (1≤limitingAngularW b θ) ↔ (1≤limitingAngularW b φ)) :
    ‖lowerProjectedPair b (θ,φ)‖ < 1 := by
  have hne (t : ℝ) (ht : h≤reflectedLowerChord b t) : limitingAngularW b t≠1 := by
    intro he
    rw [reflectedLowerChord_zero_of_branch hb he] at ht
    linarith
  have hn (t : ℝ) := (continuedRoot_real_lower_bounds (limitingAngularW_gt_neg_one hb t)).1
  have hi (t : ℝ) := (continuedRoot_real_lower_bounds (limitingAngularW_gt_neg_one hb t)).2
  have hyi (t : ℝ) : (lowerCircleProjection t).im≤0 := by
    rw [lowerCircleProjection_im]
    exact neg_nonpos.mpr (abs_nonneg _)
  by_cases hL : 1≤limitingAngularW b θ
  · have hLθ : 1<limitingAngularW b θ := lt_of_le_of_ne hL (hne θ hθ).symm
    have hLφ : 1<limitingAngularW b φ := lt_of_le_of_ne (hcolor.mp hL) (hne φ hφ).symm
    apply complete_pair_strict_left (s := s) (lowerCircleProjection_norm θ) (lowerCircleProjection_norm φ)
      (hyi θ) (hyi φ) (continuedRoot_nonzero _) (continuedRoot_nonzero _)
      (lowerProjectedRoot_quadratic s b θ hS) (lowerProjectedRoot_quadratic s b φ hS)
    · simpa [lowerProjectedRoot,continuedRoot,hLθ] using (compactLeftRoot_real_bounds hLθ).2.2
    · simpa [lowerProjectedRoot,continuedRoot,hLφ] using (compactLeftRoot_real_bounds hLφ).2.2
    · exact hi θ
    · exact hi φ
  · have hRθ : |limitingAngularW b θ|<1 := abs_lt.mpr ⟨limitingAngularW_gt_neg_one hb θ,lt_of_not_ge hL⟩
    have hRφ : |limitingAngularW b φ|<1 := abs_lt.mpr ⟨limitingAngularW_gt_neg_one hb φ,
      lt_of_not_ge (fun h => hL (hcolor.mpr h))⟩
    apply complete_pair_strict_right (s := s) (lowerCircleProjection_norm θ) (lowerCircleProjection_norm φ)
      (hyi θ) (hyi φ) (continuedRoot_nonzero _) (continuedRoot_nonzero _)
      (lowerProjectedRoot_quadratic s b θ hS) (lowerProjectedRoot_quadratic s b φ hS) (hn θ) (hn φ)
    · simpa [lowerProjectedRoot,continuedRoot,show ¬1<limitingAngularW b θ by linarith [abs_lt.mp hRθ]] using
        (compactRight_real_norm_im _ hRθ).2
    · simpa [lowerProjectedRoot,continuedRoot,show ¬1<limitingAngularW b φ by linarith [abs_lt.mp hRφ]] using
        (compactRight_real_norm_im _ hRφ).2

def compactCrossAngles (b h : ℝ) : Set (ℝ × ℝ) :=
  (Icc 0 (2*Real.pi) ×ˢ Icc 0 (2*Real.pi)) ∩
    {p | h≤reflectedLowerChord b p.1 ∨ h≤reflectedLowerChord b p.2}

def compactSameAngles (b h : ℝ) : Set (ℝ × ℝ) :=
  (Icc 0 (2*Real.pi) ×ˢ Icc 0 (2*Real.pi)) ∩
    {p | h≤reflectedLowerChord b p.1 ∧ h≤reflectedLowerChord b p.2 ∧
      ((1≤limitingAngularW b p.1 ∧ 1≤limitingAngularW b p.2) ∨
       (limitingAngularW b p.1≤1 ∧ limitingAngularW b p.2≤1))}

theorem compactCrossAngles_compact (b h : ℝ) : IsCompact (compactCrossAngles b h) := by
  have hc₁ : Continuous (fun p : ℝ × ℝ => reflectedLowerChord b p.1) := by unfold reflectedLowerChord; fun_prop
  have hc₂ : Continuous (fun p : ℝ × ℝ => reflectedLowerChord b p.2) := by unfold reflectedLowerChord; fun_prop
  exact (isCompact_Icc.prod isCompact_Icc).inter_right
    ((isClosed_le continuous_const hc₁).union (isClosed_le continuous_const hc₂))

theorem compactSameAngles_compact (b h : ℝ) : IsCompact (compactSameAngles b h) := by
  have hc₁ : Continuous (fun p : ℝ × ℝ => reflectedLowerChord b p.1) := by unfold reflectedLowerChord; fun_prop
  have hc₂ : Continuous (fun p : ℝ × ℝ => reflectedLowerChord b p.2) := by unfold reflectedLowerChord; fun_prop
  have hw₁ : Continuous (fun p : ℝ × ℝ => limitingAngularW b p.1) := by unfold limitingAngularW; fun_prop
  have hw₂ : Continuous (fun p : ℝ × ℝ => limitingAngularW b p.2) := by unfold limitingAngularW; fun_prop
  exact (isCompact_Icc.prod isCompact_Icc).inter_right
    ((isClosed_le continuous_const hc₁).inter ((isClosed_le continuous_const hc₂).inter
      (((isClosed_le continuous_const hw₁).inter (isClosed_le continuous_const hw₂)).union
        ((isClosed_le hw₁ continuous_const).inter (isClosed_le hw₂ continuous_const)))))

theorem compactSameAngles_subset_cross (b h : ℝ) : compactSameAngles b h ⊆ compactCrossAngles b h :=
  fun _ hp => ⟨hp.1,Or.inl hp.2.1⟩

theorem lowerProjectedPair_continuousAt {b h : ℝ} (hb : 0<Real.sin b) (hh : 0<h)
    {p : ℝ × ℝ} (hp : p ∈ compactCrossAngles b h) : ContinuousAt (lowerProjectedPair b) p :=
  continuousAt_canceledPair _ _ _ _ p
    (lowerCircleProjection_continuous.comp continuous_fst).continuousAt
    (lowerCircleProjection_continuous.comp continuous_snd).continuousAt
    ((lowerProjectedRoot_continuous hb).comp continuous_fst).continuousAt
    ((lowerProjectedRoot_continuous hb).comp continuous_snd).continuousAt
    (norm_ne_zero_iff.mp (by rw [lowerCircleProjection_norm]; norm_num))
    (norm_ne_zero_iff.mp (by rw [lowerCircleProjection_norm]; norm_num))
    (lowerProjectedPair_gap hb hh hp.2)

theorem lowerProjectedPair_uniform_strict (s : ℂ) {b h : ℝ}
    (hS : sourceS s=((1+Real.cos b:ℝ):ℂ)) (hb : 0<Real.sin b) (hh : 0<h) :
    ∃ q : ℝ, 0<q ∧ q<1 ∧ ∀ p ∈ compactSameAngles b h, ‖lowerProjectedPair b p‖≤q := by
  apply compact_norm_strict_bound _ _ (compactSameAngles_compact b h)
    (fun p hp => (lowerProjectedPair_continuousAt hb hh (compactSameAngles_subset_cross b h hp)).continuousWithinAt)
  intro p hp
  apply lowerProjectedPair_same_strict s hS hb hh hp.2.1 hp.2.2.1
  rcases hp.2.2.2 with hl | hr
  · exact iff_of_true hl.1 hl.2
  · have hne (t : ℝ) (ht : h≤reflectedLowerChord b t) : limitingAngularW b t≠1 := by
      intro he
      rw [reflectedLowerChord_zero_of_branch hb he] at ht
      linarith
    have hn₁ : ¬1≤limitingAngularW b p.1 := by intro he; exact hne _ hp.2.1 (le_antisymm hr.1 he)
    have hn₂ : ¬1≤limitingAngularW b p.2 := by intro he; exact hne _ hp.2.2.1 (le_antisymm hr.2 he)
    exact iff_of_false hn₁ hn₂

abbrev CompletePairTuple := (ℂ × ℂ) × (ℂ × ℂ)
def completePairTupleValue (v : CompletePairTuple) : ℂ := canceledPair v.1.1 v.1.2 v.2.1 v.2.2
def lowerProjectedTuple (b : ℝ) (p : ℝ × ℝ) : CompletePairTuple :=
  ((lowerCircleProjection p.1,lowerCircleProjection p.2),(lowerProjectedRoot b p.1,lowerProjectedRoot b p.2))

theorem lowerProjectedTuple_continuous {b : ℝ} (hb : 0<Real.sin b) :
    Continuous (lowerProjectedTuple b) :=
  ((lowerCircleProjection_continuous.comp continuous_fst).prodMk
    (lowerCircleProjection_continuous.comp continuous_snd)).prodMk
    (((lowerProjectedRoot_continuous hb).comp continuous_fst).prodMk
      ((lowerProjectedRoot_continuous hb).comp continuous_snd))

theorem compact_complete_pair_uniform_motion {b h ξ : ℝ}
    (hb : 0<Real.sin b) (hh : 0<h) (hξ : 0<ξ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ p ∈ compactCrossAngles b h, ∀ v : CompletePairTuple,
      dist (lowerProjectedTuple b p) v < δ →
      ‖completePairTupleValue v-lowerProjectedPair b p‖ < ξ := by
  let K := lowerProjectedTuple b '' compactCrossAngles b h
  have hK : IsCompact K := (compactCrossAngles_compact b h).image (lowerProjectedTuple_continuous hb)
  have hc : ∀ v ∈ K, ContinuousAt completePairTupleValue v := by
    rintro _ ⟨p,hp,rfl⟩
    apply continuousAt_canceledPair _ _ _ _ _
      (continuous_fst.fst.continuousAt) (continuous_fst.snd.continuousAt)
      (continuous_snd.fst.continuousAt) (continuous_snd.snd.continuousAt)
      (norm_ne_zero_iff.mp (by simp only [lowerProjectedTuple]; rw [lowerCircleProjection_norm]; norm_num))
      (norm_ne_zero_iff.mp (by simp only [lowerProjectedTuple]; rw [lowerCircleProjection_norm]; norm_num))
      (lowerProjectedPair_gap hb hh hp.2)
  have hu := hK.uniformContinuousAt_of_continuousAt completePairTupleValue hc
    (Metric.dist_mem_uniformity hξ)
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_uniformity_dist.mp hu
  refine ⟨δ,hδ,?_⟩
  intro p hp v hv
  have hh' := hd hv (show lowerProjectedTuple b p ∈ K from ⟨p,hp,rfl⟩)
  change dist (completePairTupleValue (lowerProjectedTuple b p)) (completePairTupleValue v) < ξ at hh'
  simpa only [dist_eq_norm,norm_sub_rev,completePairTupleValue,lowerProjectedTuple,lowerProjectedPair] using hh'

theorem protected_complete_pair_tuple_transfer (s : ℂ) {b h : ℝ}
    (hS : sourceS s=((1+Real.cos b:ℝ):ℂ)) (hb : 0<Real.sin b) (hh : 0<h) :
    ∃ q : ℝ, 0<q ∧ q<1 ∧ ∀ σ : ℝ, 0<σ → ∃ δ : ℝ, 0<δ ∧
      ∀ p ∈ compactCrossAngles b h, ∀ y v z w : ℂ,
      ‖y-lowerCircleProjection p.1‖<δ → ‖v-lowerCircleProjection p.2‖<δ →
      ‖z-lowerProjectedRoot b p.1‖<δ → ‖w-lowerProjectedRoot b p.2‖<δ →
      ‖canceledPair y v z w‖ ≤ 1+σ ∧
        (p ∈ compactSameAngles b h → ‖canceledPair y v z w‖≤q) := by
  obtain ⟨q,hq,hq1,hqb⟩ := lowerProjectedPair_uniform_strict s hS hb hh
  refine ⟨(1+q)/2,by positivity,by linarith,?_⟩
  intro σ hσ
  obtain ⟨δ,hδ,hd⟩ := compact_complete_pair_uniform_motion hb hh
    (lt_min hσ (show 0<(1-q)/2 by linarith))
  refine ⟨δ,hδ,?_⟩
  intro p hp y v z w hy hv hz hw
  have hdist : dist (lowerProjectedTuple b p) ((y,v),(z,w))<δ := by
    change max (max (dist (lowerCircleProjection p.1) y) (dist (lowerCircleProjection p.2) v))
      (max (dist (lowerProjectedRoot b p.1) z) (dist (lowerProjectedRoot b p.2) w))<δ
    rw [max_lt_iff,max_lt_iff,max_lt_iff]
    simpa only [dist_eq_norm,norm_sub_rev] using And.intro (And.intro hy hv) (And.intro hz hw)
  have hm := hd p hp ((y,v),(z,w)) hdist
  change ‖canceledPair y v z w-lowerProjectedPair b p‖ < min σ ((1-q)/2) at hm
  have hn := norm_le_norm_add_norm_sub (lowerProjectedPair b p) (canceledPair y v z w)
  rw [norm_sub_rev (lowerProjectedPair b p) (canceledPair y v z w)] at hn
  constructor
  · have hbase := lowerProjectedPair_le_one s hS hb hh hp.2
    have hδσ := hm.trans_le (min_le_left _ _)
    linarith
  · intro hs
    have hbase := hqb p hs
    have hδq := hm.trans_le (min_le_right _ _)
    linarith

theorem reflectedLowerChord_lower {b θ α : ℝ} (hb : 0≤Real.sin b) (hα : 0≤α)
    (hs : Real.sin θ≤3*α/2) :
    lowerChord b θ-6*Real.sin b*α ≤ reflectedLowerChord b θ := by
  have hsin : Real.sin θ+|Real.sin θ|≤3*α := by
    by_cases h : 0≤Real.sin θ
    · rw [abs_of_nonneg h]
      linarith
    · rw [abs_of_neg (lt_of_not_ge h)]
      linarith
  have hm := mul_le_mul_of_nonneg_left hsin (show 0≤2*Real.sin b by positivity)
  have he : lowerChord b θ-reflectedLowerChord b θ =
      2*Real.sin b*(Real.sin θ+|Real.sin θ|) := by
    unfold lowerChord reflectedLowerChord
    nlinarith [sq_abs (Real.sin θ)]
  linarith

theorem reflectedLowerChord_of_source_compact {b θ α η : ℝ}
    (hb : 0<Real.sin b) (hα : 0≤α) (hαsmall : α≤η^2/(24*Real.sin b))
    (hs : Real.sin θ≤3*α/2) (hc : η^2/2≤lowerChord b θ) :
    η^2/4≤reflectedLowerChord b θ := by
  have ha := (le_div_iff₀ (show 0<24*Real.sin b by positivity)).mp hαsmall
  have hh := reflectedLowerChord_lower hb.le hα hs
  nlinarith

theorem compactSameAngles_of_color {b h θ φ : ℝ}
    (hθ : θ∈Icc 0 (2*Real.pi)) (hφ : φ∈Icc 0 (2*Real.pi))
    (hcθ : h≤reflectedLowerChord b θ) (hcφ : h≤reflectedLowerChord b φ)
    (hcolor : (1≤limitingAngularW b θ) ↔ (1≤limitingAngularW b φ)) :
    (θ,φ) ∈ compactSameAngles b h := by
  refine ⟨⟨hθ,hφ⟩,hcθ,hcφ,?_⟩
  by_cases h : 1≤limitingAngularW b θ
  · exact Or.inl ⟨h,hcolor.mp h⟩
  · exact Or.inr ⟨(lt_of_not_ge h).le,(lt_of_not_ge (fun hh => h (hcolor.mpr hh))).le⟩

/-- The original chord mask and the upper endpoint slivers are attached.
The necessary alpha restriction is selected after eta, never assumed from
alpha<sin(b)/4 alone. -/
theorem protected_complete_pair_source_transfer (s : ℂ) {b η : ℝ}
    (hS : sourceS s=((1+Real.cos b:ℝ):ℂ)) (hb : 0<Real.sin b) (hη : 0<η) :
    ∃ q : ℝ, 0<q ∧ q<1 ∧ ∀ σ : ℝ, 0<σ → ∃ δ : ℝ, 0<δ ∧
      ∀ α θ φ : ℝ, 0≤α → α≤η^2/(24*Real.sin b) →
      θ∈Icc 0 (2*Real.pi) → φ∈Icc 0 (2*Real.pi) →
      Real.sin θ≤3*α/2 → Real.sin φ≤3*α/2 →
      (η^2/2≤lowerChord b θ ∨ η^2/2≤lowerChord b φ) →
      ∀ y v z w : ℂ,
      ‖y-lowerCircleProjection θ‖<δ → ‖v-lowerCircleProjection φ‖<δ →
      ‖z-lowerProjectedRoot b θ‖<δ → ‖w-lowerProjectedRoot b φ‖<δ →
      ‖canceledPair y v z w‖ ≤ 1+σ ∧
        ((η^2/2≤lowerChord b θ ∧ η^2/2≤lowerChord b φ ∧
          ((1≤limitingAngularW b θ) ↔ (1≤limitingAngularW b φ))) → ‖canceledPair y v z w‖≤q) := by
  obtain ⟨q,hq,hq1,htransfer⟩ := protected_complete_pair_tuple_transfer s hS hb
    (show 0<η^2/4 by positivity)
  refine ⟨q,hq,hq1,?_⟩
  intro σ hσ
  obtain ⟨δ,hδ,hd⟩ := htransfer σ hσ
  refine ⟨δ,hδ,?_⟩
  intro α θ φ hα hαsmall hθ hφ hsθ hsφ hcross y v z w hy hv hz hw
  have hcθ := reflectedLowerChord_of_source_compact hb hα hαsmall hsθ
  have hcφ := reflectedLowerChord_of_source_compact hb hα hαsmall hsφ
  have hp : (θ,φ)∈compactCrossAngles b (η^2/4) :=
    ⟨⟨hθ,hφ⟩,hcross.elim (fun h => Or.inl (hcθ h)) (fun h => Or.inr (hcφ h))⟩
  obtain ⟨hweak,hstrict⟩ := hd (θ,φ) hp y v z w hy hv hz hw
  refine ⟨hweak,?_⟩
  rintro ⟨hc₁,hc₂,hcolor⟩
  exact hstrict (compactSameAngles_of_color hθ hφ (hcθ hc₁) (hcφ hc₂) hcolor)

end
end IsingBulk.Tail
