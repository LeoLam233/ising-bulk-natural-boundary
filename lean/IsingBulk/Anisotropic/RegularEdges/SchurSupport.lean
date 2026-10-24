import IsingBulk.Tail.CompactRootGroups

/-! ANISO (3.1)--(3.4): the strict contraction is proved on the actual
anisotropic edge dispersion, not assumed for complete canceled pairs. -/
namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set

def edgeW (b : ℝ) (B : ℂ) (q : ℝ) : ℂ := (b:ℂ)+B*(1-(Real.cos q:ℂ))
def edgeRoot (b : ℝ) (B : ℂ) (q : ℝ) : ℂ := continuedRoot (edgeW b B q)

theorem edgeW_im (b : ℝ) (B : ℂ) (q : ℝ) :
    (edgeW b B q).im = B.im*(1-Real.cos q) := by
  simp only [edgeW, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.sub_im, Complex.one_im]
  ring

theorem edgeW_domain {b : ℝ} {B : ℂ} (hb : |b| < 1) (hB : 0 < B.im) (q : ℝ) :
    edgeW b B q ∈ continuedRootDomain := by
  by_cases hq : Real.cos q = 1
  · have he : edgeW b B q = (b:ℂ) := by simp [edgeW,hq]
    rw [he]
    exact Or.inr (by simpa using hb)
  · exact Or.inl (Or.inl (by change 0 < (edgeW b B q).im; rw [edgeW_im]; exact mul_pos hB (sub_pos.mpr (lt_of_le_of_ne (Real.cos_le_one q) hq))))

theorem edgeRoot_bounds {b : ℝ} {B : ℂ} (hb : |b| < 1) (hB : 0 < B.im) (q : ℝ) :
    ‖edgeRoot b B q‖ ≤ 1 ∧ (edgeRoot b B q).im < 0 := by
  by_cases hq : Real.cos q = 1
  · have he : edgeW b B q = (b:ℂ) := by simp [edgeW,hq]
    have hbre : ¬ 1 < (b:ℂ).re := by simpa using (not_lt_of_ge (le_of_lt (abs_lt.mp hb).2))
    simp only [edgeRoot,he,continuedRoot,ite_eq_right hbre]
    obtain ⟨hn,hi⟩ := compactRight_real_norm_im b hb
    exact ⟨hn.le,hi⟩
  · have hi : 0 < (edgeW b B q).im := by
      rw [edgeW_im]
      exact mul_pos hB (sub_pos.mpr (lt_of_le_of_ne (Real.cos_le_one q) hq))
    rw [edgeRoot,continuedRoot_eq_interiorRoot hi]
    exact ⟨(interiorRoot_norm_lt_one hi).le,interiorRoot_lower_im hi⟩

theorem edgeRoot_continuous {b : ℝ} {B : ℂ} (hb : |b| < 1) (hB : 0 < B.im) :
    Continuous (edgeRoot b B) := by
  rw [continuous_iff_continuousAt]
  intro q
  exact (continuedRoot_analyticAt (edgeW_domain hb hB q)).continuousAt.comp
    (by unfold edgeW; fun_prop)

/-- A single strict Schur constant controls every pair in the full real-angle
support. The compact interval contains a whole angular period. -/
theorem edgeRoot_uniform_schur {b : ℝ} {B : ℂ} (hb : |b| < 1) (hB : 0 < B.im) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ q ∈ Icc (-Real.pi) Real.pi,
      ∀ t ∈ Icc (-Real.pi) Real.pi,
        ‖pairKernel (edgeRoot b B q) (edgeRoot b B t)‖ ≤ r := by
  let K := edgeRoot b B '' Icc (-Real.pi) Real.pi
  have hK : IsCompact K := isCompact_Icc.image (edgeRoot_continuous hb hB)
  obtain ⟨r,hr,hr1,hm⟩ := compact_schur_norm_bound K hK (by
    rintro z ⟨q,hq,rfl⟩ w ⟨t,ht,rfl⟩
    obtain ⟨hnq,hiq⟩ := edgeRoot_bounds hb hB q
    obtain ⟨hnt,hit⟩ := edgeRoot_bounds hb hB t
    exact schur_normSq_lt_of_same_half hnq hnt (mul_pos_of_neg_of_neg hiq hit))
  exact ⟨r,hr,hr1,fun q hq t ht => hm _ ⟨q,hq,rfl⟩ _ ⟨t,ht,rfl⟩⟩

/-- No zero denominator has been removed by totalized division. -/
theorem edgeRoot_pair_denominator_ne_zero {b : ℝ} {B : ℂ}
    (hb : |b| < 1) (hB : 0 < B.im) (q t : ℝ) :
    1-edgeRoot b B q*edgeRoot b B t ≠ 0 := by
  obtain ⟨hnq,hiq⟩ := edgeRoot_bounds hb hB q
  obtain ⟨hnt,hit⟩ := edgeRoot_bounds hb hB t
  have hs := schur_normSq_lt_of_same_half hnq hnt (mul_pos_of_neg_of_neg hiq hit)
  intro he
  rw [he] at hs
  simp only [map_zero] at hs
  exact (not_lt_of_ge (Complex.normSq_nonneg _)) hs
end
end IsingBulk.Anisotropic.RegularEdges
