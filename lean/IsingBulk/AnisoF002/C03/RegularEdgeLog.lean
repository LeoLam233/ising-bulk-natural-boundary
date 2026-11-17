import IsingBulk.AnisoF002.C03.RegularEdgeNumerator
import IsingBulk.AnisoF002.RegularTail.PhysicalFactors

/-!
# One genuine logarithmic phase around the complete regular edge circle

The explicit spectral root has negative imaginary part wherever its
discriminant belongs to the principal square-root slit plane.  Its principal
logarithm therefore supplies one phase, not a collection of unrelated local
choices.  Compactness gives a common complex parameter/cosine neighborhood.
The finite normalization below retains the complete anisotropy power.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

theorem upperEdgeRoot_im_neg_of_slit {W : ℂ}
    (hslit : 1 - W ^ 2 ∈ Complex.slitPlane) : (upperEdgeRoot W).im < 0 := by
  by_cases hpos : 0 < W.im
  · exact upperEdgeRoot_im_neg (Or.inl hpos)
  by_cases hz : W.im = 0
  · have hre : 0 < (1 - W ^ 2).re := by
      rcases Complex.mem_slitPlane_iff.mp hslit with h | h
      · exact h
      · exfalso
        apply h
        simp [pow_two, hz]
    have hs : |W.re| < 1 := by
      apply (sq_lt_one_iff_abs_lt_one W.re).mp
      simp only [pow_two, Complex.sub_re, Complex.one_re, Complex.mul_re, hz,
        mul_zero, sub_zero] at hre
      nlinarith
    exact upperEdgeRoot_im_neg (Or.inr ⟨hz, hs⟩)
  · have hi : W.im < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hz
    have hs := sqrt_re_pos_of_slit hslit
    simp only [upperEdgeRoot, Complex.sub_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_add]
    linarith

theorem upperEdgeRoot_mem_slit {W : ℂ} (hslit : 1 - W ^ 2 ∈ Complex.slitPlane) :
    upperEdgeRoot W ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_lt (upperEdgeRoot_im_neg_of_slit hslit)))

def upperEdgePhase (W : ℂ) : ℂ := -Complex.log (upperEdgeRoot W)

theorem upperEdgePhase_analyticAt {W : ℂ} (hslit : 1 - W ^ 2 ∈ Complex.slitPlane) :
    AnalyticAt ℂ upperEdgePhase W :=
  ((upperEdgeRoot_analyticAt hslit).clog (upperEdgeRoot_mem_slit hslit)).neg

theorem upperEdgePhase_exp_neg (W : ℂ) :
    Complex.exp (-upperEdgePhase W) = upperEdgeRoot W := by
  rw [upperEdgePhase, neg_neg, Complex.exp_log (upperEdgeRoot_ne_zero W)]

theorem upperEdgePhase_cosh (W : ℂ) : Complex.cosh (upperEdgePhase W) = W := by
  have hp := upperEdgeRoot_polynomial W
  have hn := upperEdgeRoot_ne_zero W
  rw [upperEdgePhase, Complex.cosh, Complex.exp_neg, neg_neg, Complex.exp_log hn]
  field_simp
  linear_combination hp

theorem upperEdgePhase_re_nonneg {W : ℂ} (hW : upperEdgeRegion W) :
    0 ≤ (upperEdgePhase W).re := by
  have h := Real.log_nonpos (norm_nonneg (upperEdgeRoot W)) (upperEdgeRoot_norm_le_one hW)
  simpa only [upperEdgePhase, Complex.neg_re, Complex.log_re] using neg_nonneg.mpr h

theorem upperEdgePhase_re_pos {W : ℂ} (hW : 0 < W.im) :
    0 < (upperEdgePhase W).re := by
  have h := Real.log_neg (norm_pos_iff.mpr (upperEdgeRoot_ne_zero W)) (upperEdgeRoot_norm_lt_one hW)
  simpa only [upperEdgePhase, Complex.neg_re, Complex.log_re] using neg_pos.mpr h

def edgeJointPhase (c a : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  upperEdgePhase (c p.1 + a p.1 * (1 - p.2))

def edgeAnglePhase (c a : ℂ → ℂ) (t : ℂ) (q : ℝ) : ℂ :=
  edgeJointPhase c a (t, (Real.cos q : ℂ))

def edgeTotalPhase {N : ℕ} (c a : ℂ → ℂ) (t : ℂ) (x : Fin N → ℝ) : ℂ :=
  ∑ i, edgeAnglePhase c a t (x i)

theorem edgeAnglePhase_exp_neg (c a : ℂ → ℂ) (t : ℂ) (q : ℝ) :
    Complex.exp (-edgeAnglePhase c a t q) = edgeAngleRoot c a t q :=
  upperEdgePhase_exp_neg _

theorem edgeAnglePhase_cosh (c a : ℂ → ℂ) (t : ℂ) (q : ℝ) :
    Complex.cosh (edgeAnglePhase c a t q) = c t + a t * (1 - (Real.cos q : ℂ)) :=
  upperEdgePhase_cosh _

theorem edgeTotalPhase_exp_neg {N : ℕ} (c a : ℂ → ℂ) (t : ℂ) (x : Fin N → ℝ) :
    Complex.exp (-edgeTotalPhase c a t x) = ∏ i, edgeAngleRoot c a t (x i) := by
  unfold edgeTotalPhase
  rw [← Finset.sum_neg_distrib, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact edgeAnglePhase_exp_neg c a t (x i)

theorem edgeAnglePhase_boundary_re_nonneg {c a : ℂ → ℂ} {b : ℝ}
    (hc0 : c 0 = (b : ℂ)) (hb : |b| < 1) (ha0 : 0 < (a 0).im) (q : ℝ) :
    0 ≤ (edgeAnglePhase c a 0 q).re := by
  apply upperEdgePhase_re_nonneg
  rw [hc0]
  exact affine_cosine_upperRegion hb ha0 (real_cos_mem_complexCosineInterval q)

theorem edgeAnglePhase_boundary_re_pos {c a : ℂ → ℂ} {b : ℝ}
    (hc0 : c 0 = (b : ℂ)) (ha0 : 0 < (a 0).im) {q : ℝ} (hq : Real.cos q < 1) :
    0 < (edgeAnglePhase c a 0 q).re := by
  apply upperEdgePhase_re_pos
  rw [hc0]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero,
    mul_zero, zero_add]
  exact mul_pos ha0 (sub_pos.mpr hq)

theorem edgeJointPhase_base_analytic {c a : ℂ → ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ c 0) (ha : AnalyticAt ℂ a 0) (hc0 : c 0 = (b : ℂ))
    (hb : |b| < 1) (ha0 : 0 < (a 0).im) {v : ℂ} (hv : v ∈ complexCosineInterval) :
    AnalyticAt ℂ (edgeJointPhase c a) (0, v) := by
  have hregion : upperEdgeRegion (c 0 + a 0 * (1 - v)) := by
    rw [hc0]
    exact affine_cosine_upperRegion hb ha0 hv
  have hW : AnalyticAt ℂ (fun x : ℂ × ℂ => c x.1 + a x.1 * (1 - x.2)) (0, v) :=
    (hc.comp (f := fun x : ℂ × ℂ => x.1) analyticAt_fst).add
      ((ha.comp (f := fun x : ℂ × ℂ => x.1) analyticAt_fst).mul
        (analyticAt_const.sub analyticAt_snd))
  exact (upperEdgePhase_analyticAt (edge_discriminant_slit hregion)).comp
    (f := fun x : ℂ × ℂ => c x.1 + a x.1 * (1 - x.2)) hW

/-- The same actual principal-log phase is jointly analytic near the full
closed cosine interval, on one disk independent of angle or particle count. -/
theorem exists_regular_edge_phase_neighborhood {c a : ℂ → ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ c 0) (ha : AnalyticAt ℂ a 0) (hc0 : c 0 = (b : ℂ))
    (hb : |b| < 1) (ha0 : 0 < (a 0).im) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ Metric.closedBall (0 : ℂ) delta,
      ∀ v ∈ Metric.thickening delta complexCosineInterval,
        AnalyticAt ℂ (edgeJointPhase c a) (t, v) := by
  let K : Set (ℂ × ℂ) := ({0} : Set ℂ) ×ˢ complexCosineInterval
  have hK : IsCompact K := isCompact_singleton.prod complexCosineInterval_compact
  have hsub : K ⊆ {p | AnalyticAt ℂ (edgeJointPhase c a) p} := by
    intro p hp
    have ht : p.1 = 0 := Set.mem_singleton_iff.mp hp.1
    change AnalyticAt ℂ (edgeJointPhase c a) (p.1, p.2)
    rw [ht]
    exact edgeJointPhase_base_analytic hc ha hc0 hb ha0 hp.2
  obtain ⟨delta, hd, hdelta⟩ := hK.exists_cthickening_subset_open
    (isOpen_analyticAt ℂ (edgeJointPhase c a)) hsub
  refine ⟨delta / 2, half_pos hd, ?_⟩
  intro t ht v hv
  obtain ⟨v0, hv0, hvd⟩ := Metric.mem_thickening_iff.mp hv
  apply hdelta
  apply Metric.mem_cthickening_of_dist_le (t, v) (0, v0) delta K (by exact ⟨by simp, hv0⟩)
  have htd := Metric.mem_closedBall.mp ht
  simp only [Prod.dist_eq]
  exact max_le (htd.trans (half_le_self hd.le)) (hvd.le.trans (half_le_self hd.le))

/-- Exact full finite F002 normalization on the actual global logarithm.
All N one-body and N(N-1)/2 pair factors retain `sqrt(a)^(N^2)`. -/
theorem edgeFullNumerator_log_normalization {N : ℕ}
    (c a : ℂ → ℂ) (t : ℂ) (x : Fin N → ℝ) :
    edgeFullNumerator c a t x =
      edgePrefactor a t ^ (N ^ 2) * (∏ i, 1 / Complex.sinh (edgeAnglePhase c a t (x i))) *
        ∏ ij ∈ indexPairs N,
          ((Real.sin ((x ij.1 - x ij.2) / 2) : ℂ) /
            Complex.sinh ((edgeAnglePhase c a t (x ij.1) + edgeAnglePhase c a t (x ij.2)) / 2)) ^ 2 := by
  have hone (i : Fin N) : branchOneBody (edgeAngleRoot c a t) (x i) =
      1 / Complex.sinh (edgeAnglePhase c a t (x i)) := by
    unfold branchOneBody
    rw [← edgeAnglePhase_exp_neg, oneBody_exp_eq_inv_sinh]
  have hpair (ij : Fin N × Fin N) : branchCanceledPair (a t) (edgeAngleRoot c a t) (x ij.1) (x ij.2) =
      a t * (((Real.sin ((x ij.1 - x ij.2) / 2) : ℂ) /
        Complex.sinh ((edgeAnglePhase c a t (x ij.1) + edgeAnglePhase c a t (x ij.2)) / 2)) ^ 2) := by
    rw [branchCanceledPair_eq_real_sine, ← edgeAnglePhase_exp_neg c a t (x ij.1),
      ← edgeAnglePhase_exp_neg c a t (x ij.2), sinePairCoefficient_exp]
    rw [div_pow, Complex.ofReal_pow]
    ring
  unfold edgeFullNumerator branchFullNumerator
  simp_rw [hone, hpair]
  rw [Finset.prod_mul_distrib, Finset.prod_const, card_indexPairs]
  have hp := complete_anisotropy_power N (edgePrefactor a t) (a t) (edgePrefactor_sq a t)
  linear_combination (∏ i, 1 / Complex.sinh (edgeAnglePhase c a t (x i))) *
    (∏ ij ∈ indexPairs N,
      ((Real.sin ((x ij.1 - x ij.2) / 2) : ℂ) /
        Complex.sinh ((edgeAnglePhase c a t (x ij.1) + edgeAnglePhase c a t (x ij.2)) / 2)) ^ 2) * hp

end
end IsingBulk.AnisoF002.RegularTail.C03
