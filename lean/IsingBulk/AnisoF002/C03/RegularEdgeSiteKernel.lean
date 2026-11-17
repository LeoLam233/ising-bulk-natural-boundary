import IsingBulk.AnisoF002.C03.RegularEdgePhaseJets

/-!
# Pole-protected derivatives of the complete regular-edge site factor

The local Cauchy radius is chosen from the actual total phase and its
uniform linear-in-N derivative bound.  It is positive only where the
actual total phase has positive real part.  The estimate does not assume
a pole-free fixed disk and does not replace the complete root product.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set
open scoped Topology BigOperators

def phaseSiteFactor (G : ℂ) : ℂ := (1 + Complex.exp (-G)) / (1 - Complex.exp (-G))

def edgeSiteFactor {N : ℕ} (c a : ℂ → ℂ) (t : ℂ) (x : Fin N → ℝ) : ℂ :=
  phaseSiteFactor (edgeTotalPhase c a t x)

theorem edgeSiteFactor_eq_product {N : ℕ} (c a : ℂ → ℂ) (t : ℂ) (x : Fin N → ℝ) :
    edgeSiteFactor c a t x =
      (1 + ∏ i, edgeAngleRoot c a t (x i)) / (1 - ∏ i, edgeAngleRoot c a t (x i)) := by
  simp only [edgeSiteFactor, phaseSiteFactor, edgeTotalPhase_exp_neg]

theorem one_sub_exp_neg_half_ge_quarter {eta : ℝ} (he : 0 < eta) (he1 : eta ≤ 1) :
    eta / 4 ≤ 1 - Real.exp (-(eta / 2)) := by
  have hd : 0 < 1 + eta / 2 := by positivity
  have hexp := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (eta / 2))
    (Real.exp_pos (-(eta / 2))).le
  have hm : Real.exp (eta / 2) * Real.exp (-(eta / 2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hm] at hexp
  have hle : Real.exp (-(eta / 2)) ≤ 1 / (1 + eta / 2) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [hexp]
  have hid : 1 - 1 / (1 + eta / 2) = (eta / 2) / (1 + eta / 2) := by
    field_simp
    ring
  have hs : eta ^ 2 ≤ eta := by nlinarith [mul_le_mul_of_nonneg_left he1 he.le]
  calc
    eta / 4 ≤ 1 - 1 / (1 + eta / 2) := by
      rw [hid]
      apply (le_div_iff₀ hd).mpr
      nlinarith
    _ ≤ 1 - Real.exp (-(eta / 2)) := sub_le_sub_left hle 1

theorem phaseSiteFactor_denominator {G : ℂ} (hG : 0 < G.re) :
    1 - Complex.exp (-G) ≠ 0 := by
  have hn : ‖Complex.exp (-G)‖ < 1 := by
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hG)
  intro h
  have he : Complex.exp (-G) = 1 := (sub_eq_zero.mp h).symm
  simp only [he, norm_one, lt_self_iff_false] at hn

theorem phaseSiteFactor_analyticAt {G : ℂ} (hG : 0 < G.re) :
    AnalyticAt ℂ phaseSiteFactor G := by
  have he : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-z)) G := analyticAt_id.neg.cexp
  exact (analyticAt_const.add he).div (analyticAt_const.sub he) (phaseSiteFactor_denominator hG)

theorem phaseSiteFactor_norm_le {G : ℂ} {eta : ℝ}
    (he : 0 < eta) (he1 : eta ≤ 1) (hG : eta / 2 ≤ G.re) :
    ‖phaseSiteFactor G‖ ≤ 8 / eta := by
  have hn : ‖Complex.exp (-G)‖ ≤ Real.exp (-(eta / 2)) := by
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_exp.mpr (neg_le_neg hG)
  have hn1 : ‖Complex.exp (-G)‖ ≤ 1 := hn.trans
    (Real.exp_le_one_iff.mpr (by linarith))
  have hnum : ‖1 + Complex.exp (-G)‖ ≤ 2 := by
    have h := norm_add_le (1 : ℂ) (Complex.exp (-G))
    simp only [norm_one] at h
    linarith
  have hden : eta / 4 ≤ ‖1 - Complex.exp (-G)‖ := by
    have hrev := norm_sub_norm_le (1 : ℂ) (Complex.exp (-G))
    simp only [norm_one] at hrev
    exact (one_sub_exp_neg_half_ge_quarter he he1).trans
      ((sub_le_sub_left hn 1).trans hrev)
  unfold phaseSiteFactor
  rw [norm_div]
  calc
    ‖1 + Complex.exp (-G)‖ / ‖1 - Complex.exp (-G)‖ ≤ 2 / ‖1 - Complex.exp (-G)‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ 2 / (eta / 4) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = 8 / eta := by ring

namespace RegularEdgePhaseControl
variable {c a : ℂ → ℂ} (d : RegularEdgePhaseControl c a)

def siteScale : ℝ := min (d.radius / 4) (d.radius / (4 * d.phaseBound))

theorem siteScale_pos : 0 < d.siteScale :=
  lt_min (div_pos d.radius_pos (by norm_num))
    (div_pos d.radius_pos (mul_pos (by norm_num) d.phaseBound_pos))

theorem siteScale_le_quarter : d.siteScale ≤ d.radius / 4 := min_le_left _ _

theorem siteScale_phase_bound : 4 * d.phaseBound * d.siteScale ≤ d.radius := by
  have h := (le_div_iff₀ (mul_pos (show (0 : ℝ) < 4 by norm_num) d.phaseBound_pos)).mp
    (show d.siteScale ≤ d.radius / (4 * d.phaseBound) from min_le_right _ _)
  nlinarith

def siteRadius (N : ℕ) (eta : ℝ) : ℝ := eta / (N : ℝ) * d.siteScale

theorem siteRadius_pos {N : ℕ} {eta : ℝ} (hN : 0 < N) (he : 0 < eta) :
    0 < d.siteRadius N eta := mul_pos (div_pos he (Nat.cast_pos.mpr hN)) d.siteScale_pos

theorem siteRadius_le_quarter {N : ℕ} {eta : ℝ}
    (hN : 0 < N) (he1 : eta ≤ 1) : d.siteRadius N eta ≤ d.radius / 4 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hquot : eta / (N : ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hN)).mpr (he1.trans hN1)
  exact ((mul_le_mul_of_nonneg_right hquot d.siteScale_pos.le).trans_eq (one_mul _)).trans
    d.siteScale_le_quarter

theorem siteDisk_subset_half {N : ℕ} {eta : ℝ} {t : ℂ}
    (hN : 0 < N) (he1 : eta ≤ 1)
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 4)) :
    Metric.closedBall t (d.siteRadius N eta) ⊆ Metric.closedBall 0 (d.radius / 2) := by
  apply Metric.closedBall_subset_closedBall'
  have htd := Metric.mem_closedBall.mp ht
  have hr := d.siteRadius_le_quarter hN he1
  linarith

theorem siteDisk_phase_protected {N : ℕ} (x : Fin N → ℝ) {eta : ℝ} {t u : ℂ}
    (hN : 0 < N) (he : 0 < eta) (he1 : eta ≤ 1)
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 4))
    (heta : eta ≤ (edgeTotalPhase c a t x).re)
    (hu : u ∈ Metric.closedBall t (d.siteRadius N eta)) :
    eta / 2 ≤ (edgeTotalPhase c a u x).re := by
  apply d.totalPhase_real_protected x
      (Metric.closedBall_subset_closedBall (by linarith [d.radius_pos]) ht)
      (d.siteDisk_subset_half hN he1 ht hu) heta
  have hd : ‖u - t‖ ≤ d.siteRadius N eta := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hu
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  calc
    (N : ℝ) * (2 * d.phaseBound / d.radius) * ‖u - t‖ ≤
        (N : ℝ) * (2 * d.phaseBound / d.radius) * d.siteRadius N eta :=
      mul_le_mul_of_nonneg_left hd
        (mul_nonneg (Nat.cast_nonneg N) (div_nonneg (by linarith [d.phaseBound_pos]) d.radius_pos.le))
    _ = eta * (2 * d.phaseBound * d.siteScale / d.radius) := by
      unfold siteRadius
      field_simp
    _ ≤ eta / 2 := by
      have hs := d.siteScale_phase_bound
      have hp : 2 * d.phaseBound * d.siteScale / d.radius ≤ 1 / 2 :=
        (div_le_iff₀ d.radius_pos).mpr (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hp he.le]

/-- A fixed-order bound for the actual full site factor, with N^j cost and
the precise pole-order dependence on any positive phase lower bound ≤1. -/
theorem siteFactor_jet_bound {N : ℕ} (x : Fin N → ℝ) {eta : ℝ} {t : ℂ}
    (hN : 0 < N) (he : 0 < eta) (he1 : eta ≤ 1)
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 4))
    (heta : eta ≤ (edgeTotalPhase c a t x).re) (j : ℕ) :
    ‖iteratedDeriv j (fun u => edgeSiteFactor c a u x) t‖ ≤
      j.factorial * (8 / eta) / (d.siteRadius N eta) ^ j := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j (d.siteRadius_pos hN he)
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (ne_of_gt (d.siteRadius_pos hN he))]
    intro u hu
    have hprot := d.siteDisk_phase_protected x hN he he1 ht heta hu
    have han := d.totalPhase_parameter_analytic x
      (Metric.closedBall_subset_closedBall (half_le_self d.radius_pos.le)
        (d.siteDisk_subset_half hN he1 ht hu))
    exact ((phaseSiteFactor_analyticAt (by linarith : 0 < (edgeTotalPhase c a u x).re)).comp
      (f := fun v : ℂ => edgeTotalPhase c a v x) han).differentiableAt.differentiableWithinAt
  · intro u hu
    exact phaseSiteFactor_norm_le he he1
      (d.siteDisk_phase_protected x hN he he1 ht heta (Metric.sphere_subset_closedBall hu))

end RegularEdgePhaseControl
end
end IsingBulk.AnisoF002.RegularTail.C03
