import IsingBulk.Tail.CompactPairUniform

/-! Two-group compact Schur suppression. This is a reusable compact-image
lemma; attaching the selected contour's actual root image remains explicit. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set

 theorem continuedRoot_closed_upper_bounds {W : ℂ} (hD : W ∈ continuedRootDomain)
    (hi : 0 ≤ W.im) : ‖continuedRoot W‖ ≤ 1 ∧ (continuedRoot W).im ≤ 0 := by
  by_cases hip : 0 < W.im
  · rw [continuedRoot_eq_interiorRoot hip]
    exact ⟨(interiorRoot_norm_lt_one hip).le,(interiorRoot_lower_im hip).le⟩
  · have he : W.im=0 := by linarith
    have hW : W=(W.re:ℂ) := by apply Complex.ext <;> simp [he]
    by_cases hl : 1 < W.re
    · have hx : continuedRoot W=compactLeftRoot W := by simp [continuedRoot,hl]
      rw [hx,hW]
      obtain ⟨_,him,hn⟩ := compactLeftRoot_real_bounds hl
      exact ⟨hn.le,him.le⟩
    · have hr : |W.re| < 1 := by
        rcases hD with (hu | hl') | hr
        · exact False.elim (hip hu)
        · exact False.elim (hl hl')
        · exact hr
      have hx : continuedRoot W=interiorRoot W := by simp [continuedRoot,hl]
      rw [hx,hW]
      obtain ⟨hn,him⟩ := compactRight_real_norm_im W.re hr
      exact ⟨hn.le,him.le⟩

 theorem lower_disk_strict_alternative {z : ℂ} (hn : ‖z‖ ≤ 1) (hi : z.im ≤ 0)
    (hp : z ≠ 1) (hm : z ≠ -1) : ‖z‖ < 1 ∨ z.im < 0 := by
  by_cases hnorm : ‖z‖ < 1
  · exact Or.inl hnorm
  · right
    by_contra him
    have hre : ‖z‖=1 := le_antisymm hn (le_of_not_gt hnorm)
    have hzero : z.im=0 := by linarith
    have hs : z.re^2=1 := by
      have he := Complex.sq_norm z
      rw [hre,Complex.normSq_apply,hzero] at he
      nlinarith
    have hr : z.re=1 ∨ z.re= -1 := sq_eq_one_iff.mp hs
    rcases hr with hr | hr
    · exact hp (by apply Complex.ext <;> simp [hr,hzero])
    · exact hm (by apply Complex.ext <;> simp [hr,hzero])

 theorem compact_lower_disk_group_cover (K : Set ℂ) (hK : IsCompact K)
    (hn : ∀ z ∈ K, ‖z‖ ≤ 1) (hi : ∀ z ∈ K, z.im ≤ 0)
    (hp : ∀ z ∈ K, z ≠ 1) (hm : ∀ z ∈ K, z ≠ -1) :
    ∃ d : ℝ, 0 < d ∧ ∀ z ∈ K, ‖z‖ ≤ 1-d ∨ z.im ≤ -d := by
  let f : ℂ → ℝ := fun z => max (1-‖z‖) (-z.im)
  have hc : Continuous f := (continuous_const.sub continuous_norm).max Complex.continuous_im.neg
  have hpos : ∀ z ∈ K, 0 < f z := by
    intro z hz
    rcases lower_disk_strict_alternative (hn z hz) (hi z hz) (hp z hz) (hm z hz) with hh | hh
    · exact lt_of_lt_of_le (sub_pos.mpr hh) (le_max_left _ _)
    · exact lt_of_lt_of_le (neg_pos.mpr hh) (le_max_right _ _)
  by_cases hne : K.Nonempty
  · obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hne hc.continuousOn
    refine ⟨f z,hpos z hz,?_⟩
    intro w hw
    have he : f z ≤ max (1-‖w‖) (-w.im) := hmin hw
    rcases le_max_iff.mp he with he | he
    · left; linarith
    · right; linarith
  · exact ⟨1,zero_lt_one,fun z hz => False.elim (hne ⟨z,hz⟩)⟩

 theorem compact_schur_norm_bound (K : Set ℂ) (hK : IsCompact K)
    (hs : ∀ z ∈ K, ∀ w ∈ K,
      Complex.normSq (z-w) < Complex.normSq (1-z*w)) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ z ∈ K, ∀ w ∈ K, ‖pairKernel z w‖ ≤ q := by
  have hd : ∀ x ∈ K ×ˢ K, 1-x.1*x.2 ≠ 0 := by
    intro x hx he
    have hh := hs x.1 hx.1 x.2 hx.2
    rw [he] at hh
    simp only [map_zero] at hh
    exact (not_lt_of_ge (Complex.normSq_nonneg _)) hh
  have hc : ContinuousOn (fun x : ℂ × ℂ => pairKernel x.1 x.2) (K ×ˢ K) := by
    intro x hx
    exact ((continuousAt_fst.sub continuousAt_snd).div
      (continuousAt_const.sub (continuousAt_fst.mul continuousAt_snd)) (hd x hx)).continuousWithinAt
  obtain ⟨q,hq,hq1,hbound⟩ := compact_norm_strict_bound (K ×ˢ K)
    (fun x : ℂ × ℂ => pairKernel x.1 x.2) (hK.prod hK) hc
    (fun x hx => schur_norm_lt_of_normSq_lt (hs x.1 hx.1 x.2 hx.2))
  exact ⟨q,hq,hq1,fun z hz w hw => hbound (z,w) ⟨hz,hw⟩⟩

/-- Both compact covering groups have a single strict factor q<1; cross
pairs only receive the weak bound one. -/
 theorem compact_root_two_group_suppression (K : Set ℂ) (hK : IsCompact K)
    (hn : ∀ z ∈ K, ‖z‖ ≤ 1) (hi : ∀ z ∈ K, z.im ≤ 0)
    (hp : ∀ z ∈ K, z ≠ 1) (hm : ∀ z ∈ K, z ≠ -1) :
    ∃ d q : ℝ, 0 < d ∧ 0 < q ∧ q < 1 ∧
      (∀ z ∈ K, ‖z‖ ≤ 1-d ∨ z.im ≤ -d) ∧
      (∀ z ∈ K, ∀ w ∈ K,
        ((‖z‖ ≤ 1-d ∧ ‖w‖ ≤ 1-d) ∨ (z.im ≤ -d ∧ w.im ≤ -d)) → ‖pairKernel z w‖ ≤ q) ∧
      (∀ z ∈ K, ∀ w ∈ K, ‖pairKernel z w‖ ≤ 1) := by
  obtain ⟨d,hd,hcover⟩ := compact_lower_disk_group_cover K hK hn hi hp hm
  let L := K ∩ {z : ℂ | ‖z‖ ≤ 1-d}
  let R := K ∩ {z : ℂ | z.im ≤ -d}
  have hL : IsCompact L := hK.inter_right (isClosed_le continuous_norm continuous_const)
  have hR : IsCompact R := hK.inter_right (isClosed_le Complex.continuous_im continuous_const)
  obtain ⟨qL,hqL,hqL1,hLb⟩ := compact_schur_norm_bound L hL (by
    intro z hz w hw
    exact schur_normSq_lt_of_interior (by have hz' : ‖z‖ ≤ 1-d := hz.2; linarith) (by have hw' : ‖w‖ ≤ 1-d := hw.2; linarith)
      (mul_nonneg_of_nonpos_of_nonpos (hi z hz.1) (hi w hw.1)))
  obtain ⟨qR,hqR,hqR1,hRb⟩ := compact_schur_norm_bound R hR (by
    intro z hz w hw
    exact schur_normSq_lt_of_same_half (hn z hz.1) (hn w hw.1)
      (mul_pos_of_neg_of_neg (by have hz' : z.im ≤ -d := hz.2; linarith) (by have hw' : w.im ≤ -d := hw.2; linarith)))
  refine ⟨d,max qL qR,hd,lt_max_of_lt_left hqL,max_lt hqL1 hqR1,hcover,?_,?_⟩
  · intro z hz w hw hsame
    rcases hsame with hsame | hsame
    · exact (hLb z ⟨hz,hsame.1⟩ w ⟨hw,hsame.2⟩).trans (le_max_left _ _)
    · exact (hRb z ⟨hz,hsame.1⟩ w ⟨hw,hsame.2⟩).trans (le_max_right _ _)
  · intro z hz w hw
    exact schur_norm_le (hn z hz) (hn w hw) (mul_nonneg_of_nonpos_of_nonpos (hi z hz) (hi w hw))

 theorem continuedRoot_not_endpoints {W : ℂ} (hD : W ∈ continuedRootDomain) :
    continuedRoot W ≠ 1 ∧ continuedRoot W ≠ -1 := by
  have hq := continuedRoot_quadratic W
  constructor
  · intro he
    rw [he] at hq
    have hW : W=1 := by linear_combination -hq/2
    norm_num [hW,continuedRootDomain] at hD
  · intro he
    rw [he] at hq
    have hW : W= -1 := by linear_combination hq/2
    norm_num [hW,continuedRootDomain] at hD

 theorem compact_lower_disk_pair_denominator (K : Set ℂ)
    (hn : ∀ z ∈ K, ‖z‖ ≤ 1) (hi : ∀ z ∈ K, z.im ≤ 0)
    (hp : ∀ z ∈ K, z ≠ 1) (hm : ∀ z ∈ K, z ≠ -1)
    {z w : ℂ} (hz : z ∈ K) (hw : w ∈ K) : 1-z*w ≠ 0 := by
  intro hzero
  have he : z*w=1 := (sub_eq_zero.mp hzero).symm
  have heNorm : ‖z‖*‖w‖=1 := by rw [← norm_mul,he,norm_one]
  have hzNorm : ‖z‖=1 := by
    have hh := mul_le_of_le_one_right (norm_nonneg z) (hn w hw)
    exact le_antisymm (hn z hz) (by linarith)
  have heq := lower_unit_reciprocal_eq hzNorm (hi z hz) (hi w hw) hzero
  have hsq : z^2=1 := by simpa only [← heq,← pow_two] using he
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact hp z hz h
  · exact hm z hz h

end
end IsingBulk.Tail
