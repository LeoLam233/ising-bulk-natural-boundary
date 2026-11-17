import IsingBulk.AnisoF002.C03.NegativeInnerRemainderRadius
import IsingBulk.AnisoF002.C03.NegativeJointRealNumerator
import IsingBulk.AnisoF002.C03.NegativeLocalPoleMeasurable
import IsingBulk.AnisoF002.C03.NegativeMeasurableIntegral

/-!
# Actual all-angle measurable pole remainders on one common cutoff

The moving pole and every residue factor are those of the literal
physical numerator.  The measurable representative agrees with the
exact analytic remainder on the whole constructed disk.  This allows
integration over arbitrary genuine real-cycle pieces with no additional
angular regularity premise.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology

abbrev InnerAngularSet (n : ℕ) (s : ℝ) := {q : Fin n → ℝ // angularShortSquare q ≤ s}

theorem continuousOn_inner_angular_pullback {n : ℕ} {s r R : ℝ}
    {f : ℂ × (Fin n → ℝ) → ℂ}
    (hf : ContinuousOn f {p | p.1 ∈ Metric.ball 0 R})
    (hsub : Metric.ball (0 : ℂ) r ⊆ Metric.ball 0 R) :
    ContinuousOn (fun p : ℂ × InnerAngularSet n s => f (p.1, p.2.1))
      {p | p.1 ∈ Metric.ball 0 r} := by
  have hm : Continuous (fun p : ℂ × InnerAngularSet n s => (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  exact hf.comp hm.continuousOn (fun _ hp => hsub hp)

structure InnerRemainderFamily (b B : ℂ → ℂ) (φ : ℝ) (n : ℕ) (r s M kappa : ℝ) where
  pole : (Fin n → ℝ) → ℂ
  pole_continuous : ContinuousOn pole {q | angularShortSquare q ≤ s}
  remainder : ℂ → InnerAngularSet n s → ℂ
  remainder_measurable : Measurable (Function.uncurry remainder)
  pole_zero : ∀ q : InnerAngularSet n s, realPhaseAverage B φ n q (pole q) = 0
  pole_bound : ∀ q : InnerAngularSet n s, ‖pole q‖ ≤ r / (4 * (n : ℝ))
  residue_denominator_ne_zero : ∀ q : InnerAngularSet n s,
    deriv (realPhaseTotal B φ n q) (pole q) ≠ 0
  remainder_analytic : ∀ q : InnerAngularSet n s,
    AnalyticOnNhd ℂ (fun t => remainder t q) (Metric.ball 0 (r / (n : ℝ)))
  remainder_bound : ∀ q : InnerAngularSet n s, ∀ t ∈ Metric.ball (0 : ℂ) (r / (4 * (n : ℝ))),
    ‖remainder t q‖ ≤ M * Real.exp (-kappa * (n : ℝ) ^ 2) / ‖windingNormalization n‖
  exact_remainder : ∀ q : InnerAngularSet n s, ∀ t ∈ Metric.ball (0 : ℂ) (r / (n : ℝ)),
    remainder t q = dslope
      (filledPoleNumerator
        (fun u => completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 u (fun i => (q.1 i : ℂ)))
        (realPhaseAverage B φ n q) n (pole q)) (pole q) t
  exact_density : Complex.exp (-((n : ℂ) * ((φ : ℂ) * Complex.I))) = 1 →
    ∀ q : InnerAngularSet n s, ∀ t ∈ Metric.ball (0 : ℂ) (r / (n : ℝ)), t ≠ pole q →
      completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 t (fun i => (q.1 i : ℂ)) *
        phaseSiteFactor (realPhaseTotal B φ n q t) =
      (2 * completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 (pole q) (fun i => (q.1 i : ℂ)) /
        deriv (realPhaseTotal B φ n q) (pole q)) / (t - pole q) + remainder t q

set_option maxHeartbeats 1000000 in
theorem exists_actual_inner_remainder_families {b B : ℂ → ℂ} {φ : ℝ}
    (hb : AnalyticAt ℂ b 0) (hB : AnalyticAt ℂ B 0)
    (hφ : 0 < φ) (hπ : φ < Real.pi) (hBi : (B 0).im < 0)
    (hbsq : ∀ t, b t ^ 2 = B t) :
    ∃ r s M kappa : ℝ, 0 < r ∧ 0 < s ∧ 0 < M ∧ 0 < kappa ∧
      ∀ n : ℕ, 0 < n → Nonempty (InnerRemainderFamily b B φ n r s M kappa) := by
  obtain ⟨rJ, hrJ, hJ⟩ := exists_actual_joint_real_factor_control hb hB hφ hπ hBi hbsq
  obtain ⟨r, s, M, kappa, hr, hrrJ, hs, hM, hk, hrem⟩ :=
    exists_actual_inner_density_remainders_below hrJ hb hB hφ hπ hBi hbsq
  refine ⟨r, s, M, kappa, hr, hs, hM, hk, ?_⟩
  intro n hn
  obtain ⟨P, hPc, hd⟩ := hrem n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : 0 < r / (n : ℝ) := div_pos hr hnR
  have hsub : Metric.ball (0 : ℂ) (r / (n : ℝ)) ⊆ Metric.ball 0 rJ :=
    Metric.ball_subset_ball ((div_le_self hr.le hn1).trans hrrJ)
  let H : ℂ → InnerAngularSet n s → ℂ := fun t q =>
    completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 t (fun i => (q.1 i : ℂ))
  let F : ℂ → InnerAngularSet n s → ℂ := fun t q => realPhaseAverage B φ n q t
  have hHc : ContinuousOn (Function.uncurry H)
      {p : ℂ × InnerAngularSet n s | p.1 ∈ Metric.ball 0 (r / (n : ℝ))} := by
    change ContinuousOn (fun p : ℂ × InnerAngularSet n s =>
      completeNegativeNumerator n b (negativeGlobalPhase B φ) 0 p.1 (fun i => (p.2.1 i : ℂ))) _
    exact continuousOn_inner_angular_pullback (s := s) (hJ n).1 hsub
  have hFc : ContinuousOn (Function.uncurry F)
      {p : ℂ × InnerAngularSet n s | p.1 ∈ Metric.ball 0 (r / (n : ℝ))} := by
    change ContinuousOn (fun p : ℂ × InnerAngularSet n s => realPhaseAverage B φ n p.2 p.1) _
    exact continuousOn_inner_angular_pullback (s := s) (hJ n).2.1 hsub
  have hPm : Measurable (fun q : InnerAngularSet n s => P q) :=
    (continuousOn_iff_continuous_domRestrict.mp hPc).measurable
  have hPin (q : InnerAngularSet n s) : P q ∈ Metric.ball (0 : ℂ) (r / (n : ℝ)) := by
    rw [Metric.mem_ball, dist_zero_right]
    apply (hd q q.2).2.1.trans_lt
    rw [show r / (4 * (n : ℝ)) = (r / (n : ℝ)) / 4 by ring]
    linarith
  have hFd (q : InnerAngularSet n s) : DifferentiableAt ℂ (fun t => F t q) (P q) :=
    ((hJ n).2.2 q (P q) (hsub (hPin q))).differentiableAt
  have hKd (q : InnerAngularSet n s) : DifferentiableAt ℂ
      (filledPoleNumerator (fun t => H t q) (fun t => F t q) n (P q)) (P q) :=
    ((hd q q.2).2.2.2.1 (P q) (hPin q)).differentiableAt.of_dslope
  obtain ⟨G, hGm, hGe⟩ := exists_measurable_exact_pole_remainder n hHc hFc hPm hPin hFd hKd
  refine ⟨{
    pole := P
    pole_continuous := hPc
    remainder := G
    remainder_measurable := hGm
    pole_zero := fun q => (hd q q.2).1
    pole_bound := fun q => (hd q q.2).2.1
    residue_denominator_ne_zero := fun q => (hd q q.2).2.2.1
    remainder_analytic := ?_
    remainder_bound := ?_
    exact_remainder := ?_
    exact_density := ?_ }⟩
  · intro q t ht
    apply ((hd q q.2).2.2.2.1 t ht).congr
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with u hu
    exact (hGe u hu q).symm
  · intro q t ht
    have ht' : t ∈ Metric.ball (0 : ℂ) (r / (n : ℝ)) := by
      apply Metric.ball_subset_ball _ ht
      rw [show r / (4 * (n : ℝ)) = (r / (n : ℝ)) / 4 by ring]
      linarith
    rw [hGe t ht' q]
    exact (hd q q.2).2.2.2.2.1 t ht
  · intro q t ht
    exact hGe t ht q
  · intro hres q t ht hne
    rw [hGe t ht q]
    exact (hd q q.2).2.2.2.2.2 hres t hne

end
end IsingBulk.AnisoF002.NegativeHT
