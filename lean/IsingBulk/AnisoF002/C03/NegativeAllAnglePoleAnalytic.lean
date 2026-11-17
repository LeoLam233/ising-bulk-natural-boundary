import IsingBulk.AnisoF002.C03.NegativeAllAnglePole

/-!
# Analytic poles on the complete small-angle polydisk

The implicit pole depends analytically on every angular variable.  The
temperature disk, angular radius and quadratic constant are selected before
the particle number.  No winding or zero-sum condition enters this local
construction; the physical momentum constraint is imposed only afterwards.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

def allAnglePhaseAverage (n : ℕ) (g : ℂ × ℂ → ℂ)
    (a : (Fin n → ℂ) × ℂ) : ℂ :=
  centeredPhaseAverage n g (g (0, 0)) 0 a.1 a.2

theorem allAnglePhaseAverage_analyticAt (n : ℕ) (g : ℂ × ℂ → ℂ)
    (a : (Fin n → ℂ) × ℂ)
    (hg : ∀ i, AnalyticAt ℂ g (a.2, a.1 i)) :
    AnalyticAt ℂ (allAnglePhaseAverage n g) a := by
  have hs : AnalyticAt ℂ
      (fun a : (Fin n → ℂ) × ℂ => ∑ i, (g (a.2, a.1 i) - g (0, 0))) a := by
    apply Finset.analyticAt_fun_sum
    intro i _
    let proj : (Fin n → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
    have hi : AnalyticAt ℂ (fun a : (Fin n → ℂ) × ℂ => (a.2, a.1 i)) a :=
      analyticAt_snd.prod ((proj.analyticAt _).comp analyticAt_fst)
    exact ((hg i).comp_of_eq hi rfl).sub analyticAt_const
  change AnalyticAt ℂ
    (fun a : (Fin n → ℂ) × ℂ => (∑ i, (g (a.2, 0 + a.1 i) - g (0, 0))) / (n : ℂ)) a
  simpa only [zero_add] using hs.div_const (c := (n : ℂ))

theorem allAnglePhaseAverage_temp_deriv (n : ℕ) (g : ℂ × ℂ → ℂ)
    (δ : Fin n → ℂ) (t : ℂ)
    (hF : DifferentiableAt ℂ (allAnglePhaseAverage n g) (δ, t)) :
    deriv (centeredPhaseAverage n g (g (0, 0)) 0 δ) t =
      fderiv ℂ (allAnglePhaseAverage n g) (δ, t) (0, 1) := by
  exact (hF.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t δ).prodMk (hasDerivAt_id t))).deriv

theorem exists_uniform_analytic_all_angle_poles {g : ℂ × ℂ → ℂ}
    (hg : AnalyticAt ℂ g (0, 0))
    (hc : fderiv ℂ g (0, 0) (1, 0) ≠ 0)
    (heven : ∀ t δ : ℂ, g (t, -δ) = g (t, δ)) :
    ∃ r σ C : ℝ, 0 < r ∧ 0 < σ ∧ 0 < C ∧ σ ≤ r / 4 ∧
      AnalyticOnNhd ℂ g (Metric.ball (0, 0) r) ∧
      ∀ (n : ℕ), 0 < n → ∃ T : (Fin n → ℂ) → ℂ,
        AnalyticOnNhd ℂ T (Metric.ball 0 σ) ∧ T 0 = 0 ∧
        ∀ δ ∈ Metric.ball 0 σ,
          (∑ i, g (T δ, δ i)) = (n : ℂ) * g (0, 0) ∧
          ‖T δ‖ ≤ r / 8 ∧ ‖T δ‖ ≤ C * displacementSquare n δ / (n : ℝ) ∧
          deriv (centeredPhaseAverage n g (g (0, 0)) 0 δ) (T δ) ≠ 0 ∧
          (∀ t ∈ Metric.closedBall (0 : ℂ) (r / 4),
            AnalyticAt ℂ (centeredPhaseAverage n g (g (0, 0)) 0 δ) t ∧
              ‖deriv (centeredPhaseAverage n g (g (0, 0)) 0 δ) t -
                fderiv ℂ g (0, 0) (1, 0)‖ ≤ ‖fderiv ℂ g (0, 0) (1, 0)‖ / 2) ∧
          ∀ t ∈ Metric.closedBall (0 : ℂ) (r / 4),
            (∑ i, g (t, δ i)) = (n : ℂ) * g (0, 0) → t = T δ := by
  classical
  obtain ⟨r, σ, C, hr, hσ, hC, hσr, hga, hex⟩ :=
    exists_uniform_all_angle_zeros hg hc heven
  refine ⟨r, σ, C, hr, hσ, hC, hσr, hga, ?_⟩
  intro n hn
  have hex' (δ : Fin n → ℂ) (hδ : δ ∈ Metric.ball 0 σ) :=
    hex n hn δ (fun i => (norm_le_pi_norm δ i).trans_lt
      (by simpa only [Metric.mem_ball, dist_zero_right] using hδ))
  let T : (Fin n → ℂ) → ℂ := fun δ =>
    if hδ : δ ∈ Metric.ball 0 σ then (hex' δ hδ).choose else 0
  have hT (δ : Fin n → ℂ) (hδ : δ ∈ Metric.ball 0 σ) := (hex' δ hδ).choose_spec
  have hT' (δ : Fin n → ℂ) (hδ : δ ∈ Metric.ball 0 σ) :
      (∑ i, g (T δ, δ i)) = (n : ℂ) * g (0, 0) ∧
      ‖T δ‖ ≤ r / 8 ∧ ‖T δ‖ ≤ C * displacementSquare n δ / (n : ℝ) ∧
      deriv (centeredPhaseAverage n g (g (0, 0)) 0 δ) (T δ) ≠ 0 ∧
      (∀ t ∈ Metric.closedBall (0 : ℂ) (r / 4),
        AnalyticAt ℂ (centeredPhaseAverage n g (g (0, 0)) 0 δ) t ∧
          ‖deriv (centeredPhaseAverage n g (g (0, 0)) 0 δ) t -
            fderiv ℂ g (0, 0) (1, 0)‖ ≤ ‖fderiv ℂ g (0, 0) (1, 0)‖ / 2) ∧
      ∀ t ∈ Metric.closedBall (0 : ℂ) (r / 4),
        (∑ i, g (t, δ i)) = (n : ℂ) * g (0, 0) → t = T δ := by
    simpa only [T, dite_eq_left hδ] using hT δ hδ
  refine ⟨T, ?_, ?_, hT'⟩
  · intro δ hδ
    rcases hT' δ hδ with ⟨hlevel, hnorm, hquad, hderiv, hlocal, huniq⟩
    let F := allAnglePhaseAverage n g
    have hpair (i : Fin n) : (T δ, δ i) ∈ Metric.ball (0, 0) r := by
      have hi : ‖δ i‖ < σ := (norm_le_pi_norm δ i).trans_lt
        (by simpa only [Metric.mem_ball, dist_zero_right] using hδ)
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [Prod.mk_sub_mk, sub_zero, Prod.norm_def, max_lt_iff]
      constructor <;> linarith
    have hFa : AnalyticAt ℂ F (δ, T δ) :=
      allAnglePhaseAverage_analyticAt n g (δ, T δ) (fun i => hga _ (hpair i))
    have hD : fderiv ℂ F (δ, T δ) (0, 1) ≠ 0 := by
      rw [← allAnglePhaseAverage_temp_deriv n g δ (T δ) hFa.differentiableAt]
      exact hderiv
    have hTx : T δ ∈ Metric.ball (0 : ℂ) (r / 4) := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    apply analyticAt_of_unique_implicit_zeros (F := F) (T := T)
      (V := Metric.ball 0 σ) (U := Metric.ball (0 : ℂ) (r / 4))
      (Metric.isOpen_ball.mem_nhds hδ) Metric.isOpen_ball hTx hFa hD
    · intro y hy
      apply (centeredPhaseAverage_eq_zero_iff hn g (g (0, 0)) 0 y (T y)).mpr
      simpa only [zero_add] using (hT' y hy).1
    · intro y hy t ht hzero
      apply (hT' y hy).2.2.2.2.2 t (Metric.ball_subset_closedBall ht)
      simpa only [zero_add] using
        (centeredPhaseAverage_eq_zero_iff hn g (g (0, 0)) 0 y t).mp hzero
  · have h := (hT' 0 (Metric.mem_ball_self hσ)).2.2.1
    simp only [Pi.zero_apply, displacementSquare, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero, zero_div] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

end
end IsingBulk.AnisoF002.NegativeHT
