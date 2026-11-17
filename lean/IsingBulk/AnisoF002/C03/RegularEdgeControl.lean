import IsingBulk.AnisoF002.C03.RegularEdgeNeighborhood

/-!
# Constructed complete scalar control on the regular-edge common disk

The protected neighborhood supplies one compact set for all real angles.
Bounds for the actual one-body, retained sine quotient, complete pair and
anisotropy square root are then obtained by continuity and compactness.
The resulting data are proved to exist from the regular-edge dispersion;
they are not added physical premises.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set
open scoped Topology

def edgeAngleRoot (c a : ℂ → ℂ) (t : ℂ) (q : ℝ) : ℂ :=
  edgeJointRoot c a (t, (Real.cos q : ℂ))

def edgePrefactor (a : ℂ → ℂ) (t : ℂ) : ℂ := Complex.sqrt (a t)

def edgeOneBody (c a : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  2 * edgeJointRoot c a p / (1 - edgeJointRoot c a p ^ 2)

def edgeSineCoefficient (c a : ℂ → ℂ) (p : ℂ × (ℂ × ℂ)) : ℂ :=
  sinePairCoefficient (a p.1) (edgeJointRoot c a (p.1, p.2.1))
    (edgeJointRoot c a (p.1, p.2.2))

theorem edgePrefactor_sq (a : ℂ → ℂ) (t : ℂ) : edgePrefactor a t ^ 2 = a t := by
  simpa only [edgePrefactor, Complex.sqrt] using Complex.cpow_ofNat_inv_pow (a t) 2

theorem edgePrefactor_analyticAt {a : ℂ → ℂ} {t : ℂ}
    (ha : AnalyticAt ℂ a t) (hslit : a t ∈ Complex.slitPlane) :
    AnalyticAt ℂ (edgePrefactor a) t := by
  change AnalyticAt ℂ (fun z => Complex.sqrt (a z)) t
  simpa only [Complex.sqrt] using
    ha.cpow (g := fun _ : ℂ => (2⁻¹ : ℂ)) analyticAt_const hslit

theorem edgeOneBody_analyticAt {c a : ℂ → ℂ} {p : ℂ × ℂ}
    (hr : AnalyticAt ℂ (edgeJointRoot c a) p)
    (hd : 1 - edgeJointRoot c a p * edgeJointRoot c a p ≠ 0) :
    AnalyticAt ℂ (edgeOneBody c a) p := by
  exact (analyticAt_const.mul hr).div (analyticAt_const.sub (hr.pow 2))
    (by simpa only [pow_two] using hd)

theorem edgeSineCoefficient_analyticAt {c a : ℂ → ℂ} {p : ℂ × (ℂ × ℂ)}
    {rho : ℝ} (ha : AnalyticAt ℂ a p.1)
    (hp : p ∈ protectedPairSet (edgeJointRoot c a) rho) :
    AnalyticAt ℂ (edgeSineCoefficient c a) p := by
  have hm1 : AnalyticAt ℂ (fun x : ℂ × (ℂ × ℂ) => (x.1, x.2.1)) p :=
    analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have hm2 : AnalyticAt ℂ (fun x : ℂ × (ℂ × ℂ) => (x.1, x.2.2)) p :=
    analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hr1 := hp.1.comp (f := fun x : ℂ × (ℂ × ℂ) => (x.1, x.2.1)) hm1
  have hr2 := hp.2.1.comp (f := fun x : ℂ × (ℂ × ℂ) => (x.1, x.2.2)) hm2
  exact (((analyticAt_const.mul (ha.comp analyticAt_fst)).mul hr1).mul hr2).div
    ((analyticAt_const.sub (hr1.mul hr2)).pow 2) (pow_ne_zero _ hp.2.2.1)

theorem branchCanceledPair_eq_real_sine (B : ℂ) (r : ℝ → ℂ) (q s : ℝ) :
    branchCanceledPair B r q s = sinePairCoefficient B (r q) (r s) *
      (Real.sin ((q - s) / 2) ^ 2 : ℝ) := by
  unfold branchCanceledPair
  rw [canceledPair_eq_sinePair]
  simp only [Complex.ofReal_pow, Complex.ofReal_sin, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_ofNat]

theorem branchCanceledPair_norm_le_coefficient (B : ℂ) (r : ℝ → ℂ) (q s : ℝ) :
    ‖branchCanceledPair B r q s‖ ≤ ‖sinePairCoefficient B (r q) (r s)‖ := by
  rw [branchCanceledPair_eq_real_sine, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _)]
  exact (mul_le_mul_of_nonneg_left (Real.sin_sq_le_one _) (norm_nonneg _)).trans_eq (mul_one _)

structure RegularEdgeControl (c a : ℂ → ℂ) where
  radius : ℝ
  cosineRadius : ℝ
  rho : ℝ
  bodyBound : ℝ
  pairBound : ℝ
  prefactorBound : ℝ
  radius_pos : 0 < radius
  cosineRadius_pos : 0 < cosineRadius
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  bodyBound_pos : 0 < bodyBound
  pairBound_pos : 0 < pairBound
  prefactorBound_pos : 0 < prefactorBound
  coefficient_analytic : AnalyticOnNhd ℂ a (Metric.closedBall 0 radius)
  prefactor_analytic : AnalyticOnNhd ℂ (edgePrefactor a) (Metric.closedBall 0 radius)
  protected_pairs : ∀ t ∈ Metric.closedBall (0 : ℂ) radius,
    ∀ v ∈ Metric.thickening cosineRadius complexCosineInterval,
    ∀ w ∈ Metric.thickening cosineRadius complexCosineInterval,
      (t, v, w) ∈ protectedPairSet (edgeJointRoot c a) rho
  body_bound : ∀ t ∈ Metric.closedBall (0 : ℂ) radius, ∀ q : ℝ,
    ‖branchOneBody (edgeAngleRoot c a t) q‖ ≤ bodyBound
  pair_bound : ∀ t ∈ Metric.closedBall (0 : ℂ) radius, ∀ q s : ℝ,
    ‖branchCanceledPair (a t) (edgeAngleRoot c a t) q s‖ ≤ pairBound
  sine_bound : ∀ t ∈ Metric.closedBall (0 : ℂ) radius, ∀ q s : ℝ,
    ‖sinePairCoefficient (a t) (edgeAngleRoot c a t q) (edgeAngleRoot c a t s)‖ ≤ pairBound
  prefactor_bound : ∀ t ∈ Metric.closedBall (0 : ℂ) radius,
    ‖edgePrefactor a t‖ ≤ prefactorBound

/-- The complete all-angle scalar control is constructed from the actual
regular-edge analytic dispersion and the strict boundary geometry. -/
theorem exists_regular_edge_control {c a : ℂ → ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ c 0) (ha : AnalyticAt ℂ a 0) (hc0 : c 0 = (b : ℂ))
    (hb : |b| < 1) (ha0 : 0 < (a 0).im) : Nonempty (RegularEdgeControl c a) := by
  obtain ⟨delta, rho, hd, hrho, hrho1, hprotected⟩ :=
    exists_regular_edge_neighborhood hc ha hc0 hb ha0
  have hpre : AnalyticAt ℂ (edgePrefactor a) 0 :=
    edgePrefactor_analyticAt ha (Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt ha0)))
  obtain ⟨eps, heps, han⟩ := (ha.prod hpre).exists_ball_analyticOnNhd
  let r : ℝ := min delta eps / 2
  have hr : 0 < r := half_pos (lt_min hd heps)
  have hrd : r ≤ delta := (half_le_self (le_of_lt (lt_min hd heps))).trans (min_le_left _ _)
  have hre : r < eps := (half_lt_self (lt_min hd heps)).trans_le (min_le_right _ _)
  have hsub : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball 0 eps := by
    intro t ht
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp ht).trans_lt hre)
  have haa : AnalyticOnNhd ℂ a (Metric.closedBall 0 r) := fun t ht =>
    analyticAt_fst.comp (han t (hsub ht))
  have hbb : AnalyticOnNhd ℂ (edgePrefactor a) (Metric.closedBall 0 r) := fun t ht =>
    analyticAt_snd.comp (han t (hsub ht))
  have hprot : ∀ t ∈ Metric.closedBall (0 : ℂ) r,
      ∀ v ∈ complexCosineInterval, ∀ w ∈ complexCosineInterval,
      (t, v, w) ∈ protectedPairSet (edgeJointRoot c a) rho := by
    intro t ht v hv w hw
    exact hprotected t (Metric.closedBall_subset_closedBall hrd ht)
      v (Metric.self_subset_thickening hd _ hv) w (Metric.self_subset_thickening hd _ hw)
  let K1 := Metric.closedBall (0 : ℂ) r ×ˢ complexCosineInterval
  let K2 := Metric.closedBall (0 : ℂ) r ×ˢ (complexCosineInterval ×ˢ complexCosineInterval)
  have hK1 : IsCompact K1 := (isCompact_closedBall _ _).prod complexCosineInterval_compact
  have hK2 : IsCompact K2 :=
    (isCompact_closedBall _ _).prod (complexCosineInterval_compact.prod complexCosineInterval_compact)
  have hbodycont : ContinuousOn (edgeOneBody c a) K1 := by
    intro p hp
    have h := hprot p.1 hp.1 p.2 hp.2 p.2 hp.2
    exact (edgeOneBody_analyticAt h.1 h.2.2.1).continuousAt.continuousWithinAt
  have hsinecont : ContinuousOn (edgeSineCoefficient c a) K2 := by
    intro p hp
    exact (edgeSineCoefficient_analyticAt (haa p.1 hp.1)
      (hprot p.1 hp.1 p.2.1 hp.2.1 p.2.2 hp.2.2)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK1.exists_bound_of_continuousOn hbodycont
  obtain ⟨C, hC⟩ := hK2.exists_bound_of_continuousOn hsinecont
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn hbb.continuousOn
  have hbodybound : ∀ t ∈ Metric.closedBall (0 : ℂ) r, ∀ q : ℝ,
      ‖branchOneBody (edgeAngleRoot c a t) q‖ ≤ max M 0 + 1 := by
    intro t ht q
    exact (hM (t, (Real.cos q : ℂ)) ⟨ht, real_cos_mem_complexCosineInterval q⟩).trans
      ((le_max_left _ _).trans (le_add_of_nonneg_right (by norm_num)))
  have hsinebound : ∀ t ∈ Metric.closedBall (0 : ℂ) r, ∀ q s : ℝ,
      ‖sinePairCoefficient (a t) (edgeAngleRoot c a t q) (edgeAngleRoot c a t s)‖ ≤ max C 0 + 1 := by
    intro t ht q s
    exact (hC (t, (Real.cos q : ℂ), (Real.cos s : ℂ))
      ⟨ht, real_cos_mem_complexCosineInterval q, real_cos_mem_complexCosineInterval s⟩).trans
      ((le_max_left _ _).trans (le_add_of_nonneg_right (by norm_num)))
  refine ⟨{
    radius := r
    cosineRadius := delta
    rho := rho
    bodyBound := max M 0 + 1
    pairBound := max C 0 + 1
    prefactorBound := max B 0 + 1
    radius_pos := hr
    cosineRadius_pos := hd
    rho_pos := hrho
    rho_lt_one := hrho1
    bodyBound_pos := by positivity
    pairBound_pos := by positivity
    prefactorBound_pos := by positivity
    coefficient_analytic := haa
    prefactor_analytic := hbb
    protected_pairs := ?_
    body_bound := hbodybound
    pair_bound := ?_
    sine_bound := hsinebound
    prefactor_bound := ?_ }⟩
  · intro t ht v hv w hw
    exact hprotected t (Metric.closedBall_subset_closedBall hrd ht) v hv w hw
  · intro t ht q s
    exact (branchCanceledPair_norm_le_coefficient (a t) (edgeAngleRoot c a t) q s).trans
      (hsinebound t ht q s)
  · intro t ht
    exact (hB t ht).trans ((le_max_left _ _).trans (le_add_of_nonneg_right (by norm_num)))

end
end IsingBulk.AnisoF002.RegularTail.C03
