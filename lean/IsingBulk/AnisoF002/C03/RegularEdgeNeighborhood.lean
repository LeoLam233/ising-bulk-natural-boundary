import IsingBulk.AnisoF002.C03.RegularEdgeRoot
import IsingBulk.AnisoF002.C03.RegularBranchMatching
import IsingBulk.AnisoF002.C03.RegularScalarBounds
import Mathlib.Topology.MetricSpace.Thickening

/-!
# One protected complex neighborhood of the complete regular edge circle

The explicit root `upperEdgeRoot` is composed with the actual regular-edge
dispersion `c(t) + a(t) (1-v)`.  The cosine interval is compact.  Its strict
Schur bound has a uniform margin, and one tube around the entire compact
pair set preserves analyticity, every pair denominator and that margin.
The neighborhood is chosen before the particle number.  No off-physical
claim that the continued roots themselves have modulus at most one is used.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter
open scoped Topology

def complexCosineInterval : Set ℂ := Complex.ofReal '' Set.Icc (-1 : ℝ) 1

theorem complexCosineInterval_compact : IsCompact complexCosineInterval :=
  isCompact_Icc.image Complex.continuous_ofReal

theorem zero_mem_complexCosineInterval : (0 : ℂ) ∈ complexCosineInterval := by
  exact ⟨0, by constructor <;> norm_num, by simp⟩

theorem real_cos_mem_complexCosineInterval (q : ℝ) :
    (Real.cos q : ℂ) ∈ complexCosineInterval :=
  ⟨Real.cos q, ⟨Real.neg_one_le_cos q, Real.cos_le_one q⟩, rfl⟩

def edgeJointRoot (c a : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  upperEdgeRoot (c p.1 + a p.1 * (1 - p.2))

theorem edgeJointRoot_analyticAt {c a : ℂ → ℂ} {p : ℂ × ℂ}
    (hc : AnalyticAt ℂ c p.1) (ha : AnalyticAt ℂ a p.1)
    (hslit : 1 - (c p.1 + a p.1 * (1 - p.2)) ^ 2 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (edgeJointRoot c a) p := by
  have hW : AnalyticAt ℂ (fun x : ℂ × ℂ => c x.1 + a x.1 * (1 - x.2)) p :=
    (hc.comp analyticAt_fst).add
      ((ha.comp analyticAt_fst).mul (analyticAt_const.sub analyticAt_snd))
  exact (upperEdgeRoot_analyticAt hslit).comp
    (f := fun x : ℂ × ℂ => c x.1 + a x.1 * (1 - x.2)) hW

theorem affine_cosine_upperRegion {b : ℝ} {A : ℂ}
    (hb : |b| < 1) (hA : 0 < A.im) {v : ℂ} (hv : v ∈ complexCosineInterval) :
    upperEdgeRegion ((b : ℂ) + A * (1 - v)) := by
  obtain ⟨s, hs, rfl⟩ := hv
  by_cases h1 : s = 1
  · right
    simpa [h1] using And.intro (show (b : ℂ).im = 0 by simp) hb
  · left
    have hp : 0 < 1 - s := sub_pos.mpr (lt_of_le_of_ne hs.2 h1)
    simpa using mul_pos hA hp

def protectedPairSet (R : ℂ × ℂ → ℂ) (rho : ℝ) : Set (ℂ × (ℂ × ℂ)) :=
  {p | AnalyticAt ℂ R (p.1, p.2.1) ∧ AnalyticAt ℂ R (p.1, p.2.2) ∧
    1 - R (p.1, p.2.1) * R (p.1, p.2.2) ≠ 0 ∧
    ‖schur (R (p.1, p.2.1)) (R (p.1, p.2.2))‖ < rho}

theorem protectedPairSet_open (R : ℂ × ℂ → ℂ) (rho : ℝ) :
    IsOpen (protectedPairSet R rho) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  rcases hp with ⟨h1, h2, hd, hn⟩
  have hm1 : ContinuousAt (fun x : ℂ × (ℂ × ℂ) => (x.1, x.2.1)) p := by fun_prop
  have hm2 : ContinuousAt (fun x : ℂ × (ℂ × ℂ) => (x.1, x.2.2)) p := by fun_prop
  have hr1 : ContinuousAt (fun x : ℂ × (ℂ × ℂ) => R (x.1, x.2.1)) p :=
    ContinuousAt.comp (g := R) h1.continuousAt hm1
  have hr2 : ContinuousAt (fun x : ℂ × (ℂ × ℂ) => R (x.1, x.2.2)) p :=
    ContinuousAt.comp (g := R) h2.continuousAt hm2
  have hdcont : ContinuousAt (fun x : ℂ × (ℂ × ℂ) =>
      1 - R (x.1, x.2.1) * R (x.1, x.2.2)) p := continuousAt_const.sub (hr1.mul hr2)
  have hschur : ContinuousAt (fun x : ℂ × (ℂ × ℂ) =>
      schur (R (x.1, x.2.1)) (R (x.1, x.2.2))) p :=
    (hr1.sub hr2).div hdcont hd
  filter_upwards [hm1.eventually h1.eventually_analyticAt, hm2.eventually h2.eventually_analyticAt,
    hdcont.eventually_ne hd, hschur.norm.eventually (gt_mem_nhds hn)] with x hx1 hx2 hxd hxn
  exact ⟨hx1, hx2, hxd, hxn⟩

theorem edgeJointRoot_base_analytic {c a : ℂ → ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ c 0) (ha : AnalyticAt ℂ a 0) (hc0 : c 0 = (b : ℂ))
    (hb : |b| < 1) (ha0 : 0 < (a 0).im) {v : ℂ} (hv : v ∈ complexCosineInterval) :
    AnalyticAt ℂ (edgeJointRoot c a) (0, v) := by
  apply edgeJointRoot_analyticAt hc ha
  apply edge_discriminant_slit
  rw [hc0]
  exact affine_cosine_upperRegion hb ha0 hv

theorem edgeJointRoot_base_schur_lt_one {c a : ℂ → ℂ} {b : ℝ}
    (hc0 : c 0 = (b : ℂ)) (hb : |b| < 1) (ha0 : 0 < (a 0).im)
    {v w : ℂ} (hv : v ∈ complexCosineInterval) (hw : w ∈ complexCosineInterval) :
    ‖schur (edgeJointRoot c a (0, v)) (edgeJointRoot c a (0, w))‖ < 1 := by
  unfold edgeJointRoot
  simp only [hc0]
  exact upperEdgeRoot_schur_lt_one (affine_cosine_upperRegion hb ha0 hv)
    (affine_cosine_upperRegion hb ha0 hw)

theorem edgeJointRoot_base_denominator {c a : ℂ → ℂ} {b : ℝ}
    (hc0 : c 0 = (b : ℂ)) (hb : |b| < 1) (ha0 : 0 < (a 0).im)
    {v w : ℂ} (hv : v ∈ complexCosineInterval) (hw : w ∈ complexCosineInterval) :
    1 - edgeJointRoot c a (0, v) * edgeJointRoot c a (0, w) ≠ 0 := by
  unfold edgeJointRoot
  simp only [hc0]
  exact upperEdgeRoot_pair_denominator (affine_cosine_upperRegion hb ha0 hv)
    (affine_cosine_upperRegion hb ha0 hw)

/-- One common complex parameter disk and one common complex cosine tube
protect all real-angle pairs, including both endpoints and every collision.
The strict Schur margin is chosen before any particle number occurs. -/
theorem exists_regular_edge_neighborhood {c a : ℂ → ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ c 0) (ha : AnalyticAt ℂ a 0) (hc0 : c 0 = (b : ℂ))
    (hb : |b| < 1) (ha0 : 0 < (a 0).im) :
    ∃ delta rho : ℝ, 0 < delta ∧ 0 < rho ∧ rho < 1 ∧
      ∀ t ∈ Metric.closedBall (0 : ℂ) delta,
      ∀ v ∈ Metric.thickening delta complexCosineInterval,
      ∀ w ∈ Metric.thickening delta complexCosineInterval,
        (t, v, w) ∈ protectedPairSet (edgeJointRoot c a) rho := by
  let Q := complexCosineInterval
  let R := edgeJointRoot c a
  have hQ : IsCompact Q := complexCosineInterval_compact
  have hQne : Q.Nonempty := ⟨0, zero_mem_complexCosineInterval⟩
  have hcont : ContinuousOn (fun p : ℂ × ℂ => ‖schur (R (0, p.1)) (R (0, p.2))‖)
      (Q ×ˢ Q) := by
    intro p hp
    have hr1 : ContinuousAt (fun x : ℂ × ℂ => R (0, x.1)) p :=
      ContinuousAt.comp (g := R)
        (edgeJointRoot_base_analytic hc ha hc0 hb ha0 hp.1).continuousAt
        (show ContinuousAt (fun x : ℂ × ℂ => ((0 : ℂ), x.1)) p from
          continuousAt_const.prodMk continuousAt_fst)
    have hr2 : ContinuousAt (fun x : ℂ × ℂ => R (0, x.2)) p :=
      ContinuousAt.comp (g := R)
        (edgeJointRoot_base_analytic hc ha hc0 hb ha0 hp.2).continuousAt
        (show ContinuousAt (fun x : ℂ × ℂ => ((0 : ℂ), x.2)) p from
          continuousAt_const.prodMk continuousAt_snd)
    exact ((hr1.sub hr2).div (continuousAt_const.sub (hr1.mul hr2))
      (edgeJointRoot_base_denominator hc0 hb ha0 hp.1 hp.2)).norm.continuousWithinAt
  obtain ⟨p, hp, hpmax⟩ := (hQ.prod hQ).exists_isMaxOn (hQne.prod hQne) hcont
  let rho : ℝ := (‖schur (R (0, p.1)) (R (0, p.2))‖ + 1) / 2
  have hlt := edgeJointRoot_base_schur_lt_one hc0 hb ha0 hp.1 hp.2
  have hrho0 : 0 < rho := by dsimp [rho]; positivity
  have hrho1 : rho < 1 := by dsimp [rho, R]; linarith
  have hmargin : ∀ v ∈ Q, ∀ w ∈ Q, ‖schur (R (0, v)) (R (0, w))‖ < rho := by
    intro v hv w hw
    have hh := (isMaxOn_iff.mp hpmax) (v, w) (show (v, w) ∈ Q ×ˢ Q from ⟨hv, hw⟩)
    dsimp [rho]
    dsimp [R] at hh ⊢
    linarith
  let K : Set (ℂ × (ℂ × ℂ)) := ({0} : Set ℂ) ×ˢ (Q ×ˢ Q)
  have hK : IsCompact K := isCompact_singleton.prod (hQ.prod hQ)
  have hsub : K ⊆ protectedPairSet R rho := by
    intro x hx
    rcases hx with ⟨hx0, hx1, hx2⟩
    have he : x.1 = 0 := Set.mem_singleton_iff.mp hx0
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [he]
      exact edgeJointRoot_base_analytic hc ha hc0 hb ha0 hx1
    · rw [he]
      exact edgeJointRoot_base_analytic hc ha hc0 hb ha0 hx2
    · rw [he]
      exact edgeJointRoot_base_denominator hc0 hb ha0 hx1 hx2
    · rw [he]
      exact hmargin _ hx1 _ hx2
  obtain ⟨delta, hd, htube⟩ := hK.exists_cthickening_subset_open (protectedPairSet_open R rho) hsub
  refine ⟨delta / 2, rho, half_pos hd, hrho0, hrho1, ?_⟩
  intro t ht v hv w hw
  obtain ⟨v0, hv0, hvd⟩ := Metric.mem_thickening_iff.mp hv
  obtain ⟨w0, hw0, hwd⟩ := Metric.mem_thickening_iff.mp hw
  apply htube
  apply Metric.mem_cthickening_of_dist_le (t, v, w) (0, v0, w0) delta K
    (show (0, v0, w0) ∈ K from ⟨by simp, hv0, hw0⟩)
  have htd := Metric.mem_closedBall.mp ht
  simp only [Prod.dist_eq]
  exact max_le (htd.trans (half_le_self hd.le))
    (max_le (hvd.le.trans (half_le_self hd.le)) (hwd.le.trans (half_le_self hd.le)))

end
end IsingBulk.AnisoF002.RegularTail.C03
