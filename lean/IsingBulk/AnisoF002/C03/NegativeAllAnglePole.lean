import IsingBulk.AnisoF002.C03.NegativeEvenPhaseBounds
import IsingBulk.AnisoF002.C03.NegativePoleAnalytic

/-!
# The actual simple phase pole for every small angular tuple

Evenness removes the linear angular term without imposing a zero-sum
constraint.  One fixed temperature disk and one angular neighborhood are
chosen before the particle number.  Thus the construction covers all inner
winding sectors, including those beyond the two first windings.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem evenPhaseAverage_quadratic_bound (n : ℕ) (g : ℂ × ℂ → ℂ)
    (δ : Fin n → ℂ) (M : ℝ)
    (hzero : fderiv ℂ g (0, 0) (0, 1) = 0)
    (hquad : ∀ i, ‖g (0, δ i) - g (0, 0) -
        fderiv ℂ g (0, 0) ((0, δ i) - (0, 0))‖ ≤
      M * ‖((0, δ i) : ℂ × ℂ) - (0, 0)‖ ^ 2) :
    ‖centeredPhaseAverage n g (g (0, 0)) 0 δ 0‖ ≤
      M * displacementSquare n δ / (n : ℝ) := by
  have hlin (i : Fin n) : fderiv ℂ g (0, 0) ((0, δ i) - (0, 0)) = 0 := by
    have he : ((0, δ i) : ℂ × ℂ) - (0, 0) = δ i • ((0, 1) : ℂ × ℂ) := by
      ext <;> simp
    rw [he, map_smul, hzero, smul_zero]
  have hnorm (i : Fin n) : ‖((0, δ i) : ℂ × ℂ) - (0, 0)‖ = ‖δ i‖ := by
    simp [Prod.norm_def]
  have hb (i : Fin n) : ‖g (0, δ i) - g (0, 0)‖ ≤ M * ‖δ i‖ ^ 2 := by
    simpa only [hlin, sub_zero, hnorm] using hquad i
  have hsum := (norm_sum_le Finset.univ (fun i => g (0, δ i) - g (0, 0))).trans
    (Finset.sum_le_sum (fun i _ => hb i))
  simp only [← Finset.mul_sum] at hsum
  unfold centeredPhaseAverage
  simp only [zero_add, norm_div, norm_natCast]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n)

theorem exists_uniform_all_angle_zeros {g : ℂ × ℂ → ℂ}
    (hg : AnalyticAt ℂ g (0, 0))
    (hc : fderiv ℂ g (0, 0) (1, 0) ≠ 0)
    (heven : ∀ t δ : ℂ, g (t, -δ) = g (t, δ)) :
    ∃ r σ C : ℝ, 0 < r ∧ 0 < σ ∧ 0 < C ∧ σ ≤ r / 4 ∧
      AnalyticOnNhd ℂ g (Metric.ball (0, 0) r) ∧
      ∀ (n : ℕ), 0 < n → ∀ δ : Fin n → ℂ, (∀ i, ‖δ i‖ < σ) →
        ∃ T : ℂ,
          (∑ i, g (T, δ i)) = (n : ℂ) * g (0, 0) ∧
          ‖T‖ ≤ r / 8 ∧ ‖T‖ ≤ C * displacementSquare n δ / (n : ℝ) ∧
          deriv (centeredPhaseAverage n g (g (0, 0)) 0 δ) T ≠ 0 ∧
          (∀ t ∈ Metric.closedBall (0 : ℂ) (r / 4),
            AnalyticAt ℂ (centeredPhaseAverage n g (g (0, 0)) 0 δ) t ∧
              ‖deriv (centeredPhaseAverage n g (g (0, 0)) 0 δ) t -
                fderiv ℂ g (0, 0) (1, 0)‖ ≤ ‖fderiv ℂ g (0, 0) (1, 0)‖ / 2) ∧
          ∀ t ∈ Metric.closedBall (0 : ℂ) (r / 4),
            (∑ i, g (t, δ i)) = (n : ℂ) * g (0, 0) → t = T := by
  obtain ⟨r, M, hr, hM, hlocal, _, hquad⟩ := analytic_phase_uniform_estimates hg hc
  let a : ℂ := fderiv ℂ g (0, 0) (1, 0)
  have ha : 0 < ‖a‖ := norm_pos_iff.mpr hc
  let σ : ℝ := min (r / 4) (min 1 (‖a‖ * r / (16 * M)))
  have hσ : 0 < σ := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hσr : σ ≤ r / 4 := min_le_left _ _
  have hσ1 : σ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hσfrac : σ ≤ ‖a‖ * r / (16 * M) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hMσ : M * σ ≤ ‖a‖ * r / 16 := by
    have he := (le_div_iff₀ (by positivity : 0 < 16 * M)).mp hσfrac
    nlinarith
  have hσsq : σ ^ 2 ≤ σ := by nlinarith
  let C : ℝ := 2 * M / ‖a‖
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨r, σ, C, hr, hσ, hC, hσr, (fun p hp => (hlocal p hp).1), ?_⟩
  intro n hn δ hδ
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp (t : ℂ) (ht : t ∈ Metric.closedBall (0 : ℂ) (r / 4)) (i : Fin n) :
      (t, δ i) ∈ Metric.ball (0, 0) r := by
    have htt : ‖t‖ ≤ r / 4 := by simpa only [Metric.mem_closedBall, dist_zero_right] using ht
    have hi := hδ i
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [Prod.mk_sub_mk, sub_zero, Prod.norm_def, max_lt_iff]
    constructor <;> linarith
  have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (r / 4) :=
    Metric.mem_closedBall_self (by positivity)
  let F := centeredPhaseAverage n g (g (0, 0)) 0 δ
  have hFa (t : ℂ) (ht : t ∈ Metric.closedBall (0 : ℂ) (r / 4)) :
      AnalyticAt ℂ F t := by
    have hsum : AnalyticAt ℂ (fun u : ℂ => ∑ i, (g (u, δ i) - g (0, 0))) t := by
      apply Finset.analyticAt_fun_sum
      intro i _
      exact ((hlocal _ (hp t ht i)).1.comp (f := fun u : ℂ => (u, δ i))
        (analyticAt_id.prod analyticAt_const)).sub analyticAt_const
    change AnalyticAt ℂ
      (fun u : ℂ => (∑ i, (g (u, 0 + δ i) - g (0, 0))) / (n : ℂ)) t
    simpa only [zero_add] using hsum.div_const (c := (n : ℂ))
  have hclose (t : ℂ) (ht : t ∈ Metric.closedBall (0 : ℂ) (r / 4)) :
      ‖deriv F t - a‖ ≤ ‖a‖ / 2 := by
    apply centeredPhaseAverage_deriv_close n g (g (0, 0)) 0 a δ t hn
    · intro i
      simpa only [zero_add] using (hlocal _ (hp t ht i)).1.differentiableAt
    · intro i
      simpa only [zero_add] using (hlocal _ (hp t ht i)).2
  have hF0 : ‖F 0‖ ≤ M * displacementSquare n δ / (n : ℝ) :=
    evenPhaseAverage_quadratic_bound n g δ M
      (even_phase_angular_derivative_zero hg.differentiableAt heven)
      (fun i => hquad (0, 0) (Metric.mem_ball_self hr) (0, δ i) (hp 0 h0 i))
  have hQ : displacementSquare n δ ≤ (n : ℝ) * σ ^ 2 := by
    have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show ‖δ i‖ ^ 2 ≤ σ ^ 2 by nlinarith [hδ i, norm_nonneg (δ i)])
    simpa only [displacementSquare, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using he
  have hQavg : displacementSquare n δ / (n : ℝ) ≤ σ ^ 2 :=
    (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hQ)
  have hsmall : ‖F 0‖ / ‖a‖ ≤ r / 16 := by
    calc
      ‖F 0‖ / ‖a‖ ≤ (M * displacementSquare n δ / (n : ℝ)) / ‖a‖ := by gcongr
      _ = M * (displacementSquare n δ / (n : ℝ)) / ‖a‖ := by ring
      _ ≤ M * σ ^ 2 / ‖a‖ := by gcongr
      _ ≤ M * σ / ‖a‖ := by gcongr
      _ ≤ r / 16 := (div_le_iff₀ ha).mpr (by nlinarith [hMσ])
  obtain ⟨T, _, hFT, hdist, hderiv, huniq⟩ := exists_unique_zero_of_deriv_close hc
    (show 0 ≤ r / 4 by positivity) (fun t ht => (hFa t ht).differentiableAt)
    hclose (by linarith [hsmall])
  have hlevel : (∑ i, g (T, δ i)) = (n : ℂ) * g (0, 0) := by
    simpa only [zero_add] using
      (centeredPhaseAverage_eq_zero_iff hn g (g (0, 0)) 0 δ T).mp hFT
  refine ⟨T, hlevel, ?_, ?_, hderiv, (fun t ht => ⟨hFa t ht, hclose t ht⟩), ?_⟩
  · have he : 2 * ‖F 0‖ / ‖a‖ ≤ r / 8 := by
      calc
        _ = 2 * (‖F 0‖ / ‖a‖) := by ring
        _ ≤ r / 8 := by linarith [hsmall]
    simpa only [sub_zero] using hdist.trans he
  · have he : 2 * ‖F 0‖ / ‖a‖ ≤ C * displacementSquare n δ / (n : ℝ) := by
      calc
        _ ≤ 2 * (M * displacementSquare n δ / (n : ℝ)) / ‖a‖ := by gcongr
        _ = _ := by dsimp [C]; ring
    simpa only [sub_zero] using hdist.trans he
  · intro t ht hlevel
    apply huniq t ht
    apply (centeredPhaseAverage_eq_zero_iff hn g (g (0, 0)) 0 δ t).mpr
    simpa only [zero_add] using hlevel

end
end IsingBulk.AnisoF002.NegativeHT
