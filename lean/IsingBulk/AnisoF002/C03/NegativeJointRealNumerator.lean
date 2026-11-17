import IsingBulk.AnisoF002.C03.NegativeGlobalNumeratorControl
import IsingBulk.AnisoF002.C03.NegativeInnerPoleData
import IsingBulk.AnisoF002.C03.RegularEdgeJointDensity

/-!
# Common joint continuity of the literal negative-edge factors

The temperature disk is chosen before the number of particles and before
all real angular tuples.  The original numerator, its W_n normalization,
and the actual centered phase are kept exactly.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem realPhaseTotal_eq_edge (B : ℂ → ℂ) (φ : ℝ) (n : ℕ)
    (q : Fin n → ℝ) (t : ℂ) :
    realPhaseTotal B φ n q t =
      edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) t q := by
  simp only [realPhaseTotal, edgeTotalPhase, negativeGlobalPhase_real]

theorem realPhaseAverage_eq_total (B : ℂ → ℂ) (φ : ℝ) (n : ℕ)
    (q : Fin n → ℝ) (t : ℂ) :
    realPhaseAverage B φ n q t =
      (realPhaseTotal B φ n q t - (n : ℂ) * ((φ : ℂ) * Complex.I)) / (n : ℂ) := by
  simp only [realPhaseAverage, centeredPhaseAverage, realPhaseTotal, zero_add,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem exists_actual_joint_real_factor_control {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ r : ℝ, 0 < r ∧ ∀ n : ℕ,
      ContinuousOn (fun p : ℂ × (Fin n → ℝ) =>
        completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 p.1 (fun i => (p.2 i : ℂ)))
        {p | p.1 ∈ Metric.ball 0 r} ∧
      ContinuousOn (fun p : ℂ × (Fin n → ℝ) => realPhaseAverage B φ n p.2 p.1)
        {p | p.1 ∈ Metric.ball 0 r} ∧
      ∀ q : Fin n → ℝ, AnalyticOnNhd ℂ (realPhaseAverage B φ n q) (Metric.ball 0 r) := by
  obtain ⟨⟨dn⟩, ⟨dp⟩⟩ := exists_negative_global_controls hB hφ hπ hBi
  obtain ⟨ζ, _, _, he⟩ := eventually_negative_complete_numerator_all_indices φ hb hB hBi hbsq
  obtain ⟨s, hs, hse⟩ := Metric.eventually_nhds_iff.mp he
  let r := min s (min dn.radius dp.radius)
  have hr : 0 < r := lt_min hs (lt_min dn.radius_pos dp.radius_pos)
  have hrs : r ≤ s := min_le_left _ _
  have hrn : r ≤ dn.radius := (min_le_right _ _).trans (min_le_left _ _)
  have hrp : r ≤ dp.radius := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, hr, ?_⟩
  intro n
  have hm : Continuous (fun p : ℂ × (Fin n → ℝ) => (p.1, complexAngles p.2)) :=
    continuous_fst.prodMk ((complexAngles_continuous n).comp continuous_snd)
  have hn (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) r) : t ∈ Metric.closedBall 0 dn.radius :=
    Metric.closedBall_subset_closedBall hrn (Metric.ball_subset_closedBall ht)
  have hp (t : ℂ) (ht : t ∈ Metric.ball (0 : ℂ) r) : t ∈ Metric.closedBall 0 dp.radius :=
    Metric.closedBall_subset_closedBall hrp (Metric.ball_subset_closedBall ht)
  have hcos (q : Fin n → ℝ) (i : Fin n) : Complex.cos (complexAngles q i) = (Real.cos (q i) : ℂ) := by
    simp only [complexAngles, Complex.ofReal_cos]
  have hN : ContinuousOn (fun p : ℂ × (Fin n → ℝ) =>
      edgeFullNumerator (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) p.1 p.2)
      {p | p.1 ∈ Metric.ball 0 r} := by
    intro p ht
    have hc := (dn.jointNumerator_analytic (hn p.1 ht) (fun i => by
      rw [hcos]
      exact Metric.self_subset_thickening dn.cosineRadius_pos _
        (real_cos_mem_complexCosineInterval (p.2 i)))).continuousAt.comp hm.continuousAt
    simpa only [Function.comp_def, edgeJointNumerator_real] using hc.continuousWithinAt
  have hG : ContinuousOn (fun p : ℂ × (Fin n → ℝ) => realPhaseTotal B φ n p.2 p.1)
      {p | p.1 ∈ Metric.ball 0 r} := by
    intro p ht
    have hc := (dp.jointTotalPhase_analytic (hp p.1 ht) (fun i => by
      rw [hcos]
      exact Metric.self_subset_thickening dp.cosineRadius_pos _
        (real_cos_mem_complexCosineInterval (p.2 i)))).continuousAt.comp hm.continuousAt
    simpa only [Function.comp_def, edgeJointTotalPhase_real, realPhaseTotal_eq_edge] using hc.continuousWithinAt
  refine ⟨?_, ?_, ?_⟩
  · apply (continuousOn_const.mul hN).congr
    intro p ht
    exact hse (Metric.ball_subset_ball hrs ht) n p.2
  · simpa only [realPhaseAverage_eq_total, Pi.sub_apply] using
      (hG.sub continuousOn_const).div_const (n : ℂ)
  · intro q t ht
    have ha := dp.totalPhase_parameter_analytic q (hp t ht)
    have heq : realPhaseAverage B φ n q = fun u =>
        (edgeTotalPhase (negativeGlobalCenter B φ) (negativeGlobalCoefficient B) u q -
          (n : ℂ) * ((φ : ℂ) * Complex.I)) / (n : ℂ) := by
      funext u
      rw [realPhaseAverage_eq_total, realPhaseTotal_eq_edge]
    rw [heq]
    simpa only [Pi.sub_apply] using
      (ha.sub (analyticAt_const (v := (n : ℂ) * ((φ : ℂ) * Complex.I)))).div_const (c := (n : ℂ))

end
end IsingBulk.AnisoF002.NegativeHT
