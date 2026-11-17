import IsingBulk.AnisoF002.C03.NegativeMeasurablePole
import IsingBulk.AnisoF002.C03.RegularCompactAnalytic

/-!
# Integrating a bounded measurable analytic family

Angular continuity is unnecessary after exact pole subtraction.  Joint
measurability, slice analyticity, and the proved common Gaussian bound
give a genuine analytic integral and its Cauchy bounds.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem integral_hasDerivAt_of_measurable_analytic_disk {F : ℂ → X → ℂ}
    {R M : ℝ} (hR : 0 < R) (hF : Measurable (Function.uncurry F))
    (ha : ∀ x, AnalyticOnNhd ℂ (fun t => F t x) (Metric.closedBall 0 R))
    (hb : ∀ x t, t ∈ Metric.closedBall (0 : ℂ) R → ‖F t x‖ ≤ M)
    {u : ℂ} (hu : u ∈ Metric.ball (0 : ℂ) (R / 2)) :
    Integrable (fun x => deriv (fun t => F t x) u) μ ∧
      HasDerivAt (fun t => ∫ x, F t x ∂μ)
        (∫ x, deriv (fun t => F t x) u ∂μ) u := by
  have hsub : Metric.closedBall (0 : ℂ) (R / 2) ⊆ Metric.closedBall 0 R :=
    Metric.closedBall_subset_closedBall (half_le_self hR.le)
  have hmeas (t : ℂ) : AEStronglyMeasurable (F t) μ :=
    (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hbound (x : X) (t : ℂ) (ht : t ∈ Metric.closedBall (0 : ℂ) (R / 2)) :
      ‖deriv (fun v => F v x) t‖ ≤ M / (R / 2) := by
    simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] using
      common_disk_iteratedDeriv_bound hR (ha x) (hb x) ht 1
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := fun t x => deriv (fun v => F v x) t)
    (bound := fun _ => M / (R / 2))
    (Metric.closedBall_mem_nhds_of_mem hu)
  · exact Eventually.of_forall hmeas
  · exact (integrable_const M).mono' (hmeas u)
      (Eventually.of_forall fun x => hb x u (hsub (Metric.ball_subset_closedBall hu)))
  · exact (measurable_deriv_at_moving_center hF measurable_const
      (fun x => (ha x u (hsub (Metric.ball_subset_closedBall hu))).differentiableAt)).aestronglyMeasurable
  · exact Eventually.of_forall hbound
  · exact integrable_const _
  · exact Eventually.of_forall fun x t ht => (ha x t (hsub ht)).differentiableAt.hasDerivAt

theorem analytic_integral_of_measurable_analytic_disk {F : ℂ → X → ℂ}
    {R M : ℝ} (hR : 0 < R) (hF : Measurable (Function.uncurry F))
    (ha : ∀ x, AnalyticOnNhd ℂ (fun t => F t x) (Metric.closedBall 0 R))
    (hb : ∀ x t, t ∈ Metric.closedBall (0 : ℂ) R → ‖F t x‖ ≤ M) :
    AnalyticOnNhd ℂ (fun t => ∫ x, F t x ∂μ) (Metric.ball 0 (R / 2)) ∧
      ∀ t ∈ Metric.closedBall (0 : ℂ) R,
        ‖∫ x, F t x ∂μ‖ ≤ M * μ.real univ := by
  constructor
  · apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
    intro u hu
    exact (integral_hasDerivAt_of_measurable_analytic_disk hR hF ha hb hu).2.differentiableAt.differentiableWithinAt
  · intro t ht
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => hb x t ht)

theorem measurable_analytic_integral_normalized_jets {F : ℂ → X → ℂ}
    {R M : ℝ} (hR : 0 < R) (hF : Measurable (Function.uncurry F))
    (ha : ∀ x, AnalyticOnNhd ℂ (fun t => F t x) (Metric.closedBall 0 R))
    (hb : ∀ x t, t ∈ Metric.closedBall (0 : ℂ) R → ‖F t x‖ ≤ M) (j : ℕ) :
    ‖iteratedDeriv j (fun t => ∫ x, F t x ∂μ) 0 / (j.factorial : ℂ)‖ ≤
      M * μ.real univ / (R / 8) ^ j := by
  obtain ⟨hI, hIb⟩ := analytic_integral_of_measurable_analytic_disk (μ := μ) hR hF ha hb
  have hsub : Metric.closedBall (0 : ℂ) (R / 4) ⊆ Metric.ball 0 (R / 2) :=
    Metric.closedBall_subset_ball (by linarith)
  have hj := common_disk_iteratedDeriv_bound (by positivity : 0 < R / 4)
    (hI.mono hsub)
    (fun u hu => hIb u (Metric.closedBall_subset_closedBall (by linarith) hu))
    (Metric.mem_closedBall_self (by positivity : 0 ≤ (R / 4) / 2)) j
  have hj0 : (0 : ℝ) < j.factorial := by exact_mod_cast j.factorial_pos
  rw [norm_div, norm_natCast]
  apply (div_le_iff₀ hj0).mpr
  convert hj using 1
  ring

end
end IsingBulk.AnisoF002.NegativeHT
