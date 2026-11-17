import IsingBulk.AnisoF002.C03.NegativePhaseAverage

/-!
# A dimension-independent zero-sum moving-pole neighborhood

The normalized full phase sum is contracted on a fixed complex temperature
disk.  The angular radius is chosen once from the single analytic phase,
before the particle number and before its center.  The exact zero-sum
constraint gives the quantitative displacement bound C * sum |v_i|^2 / n.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem centeredPhaseAverage_eq_zero_iff {n : ℕ} (hn : 0 < n)
    (g : ℂ × ℂ → ℂ) (γ d : ℂ) (v : Fin n → ℂ) (t : ℂ) :
    centeredPhaseAverage n g γ d v t = 0 ↔
      (∑ i, g (t, d + v i)) = (n : ℂ) * γ := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold centeredPhaseAverage
  rw [div_eq_zero_iff, or_iff_left hn0, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_eq_zero]

theorem exists_uniform_zero_sum_phase_zeros {g : ℂ × ℂ → ℂ}
    (hg : AnalyticAt ℂ g (0, 0))
    (hc : fderiv ℂ g (0, 0) (1, 0) ≠ 0) :
    ∃ r σ C : ℝ, 0 < r ∧ 0 < σ ∧ 0 < C ∧ σ ≤ r / 4 ∧
      AnalyticOnNhd ℂ g (Metric.ball (0, 0) r) ∧
      ∀ (n : ℕ), 0 < n → ∀ τ d γ : ℂ,
        ‖τ‖ < r / 4 → ‖d‖ < r / 4 → g (τ, d) = γ →
        ∀ v : Fin n → ℂ, (∑ i, v i) = 0 → (∀ i, ‖v i‖ < σ) →
          ∃ t : ℂ,
            (∑ i, g (t, d + v i)) = (n : ℂ) * γ ∧
            ‖t - τ‖ ≤ r / 8 ∧
            ‖t - τ‖ ≤ C * displacementSquare n v / (n : ℝ) ∧
            deriv (centeredPhaseAverage n g γ d v) t ≠ 0 ∧
            ∀ u ∈ Metric.closedBall τ (r / 4),
              (∑ i, g (u, d + v i)) = (n : ℂ) * γ → u = t := by
  obtain ⟨r, M, hr, hM, hlocal, _, hquad⟩ := analytic_phase_uniform_estimates hg hc
  let c : ℂ := fderiv ℂ g (0, 0) (1, 0)
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  let σ : ℝ := min (r / 4) (min 1 (‖c‖ * r / (16 * M)))
  have hσ : 0 < σ := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hσr : σ ≤ r / 4 := min_le_left _ _
  have hσ1 : σ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hσfrac : σ ≤ ‖c‖ * r / (16 * M) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hMσ : M * σ ≤ ‖c‖ * r / 16 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 16 * M)).mp hσfrac
    nlinarith
  have hσsq : σ ^ 2 ≤ σ := by nlinarith
  let C : ℝ := 2 * M / ‖c‖
  refine ⟨r, σ, C, hr, hσ, by dsimp [C]; positivity,
    hσr, (fun p hp => (hlocal p hp).1), ?_⟩
  intro n hn τ d γ hτ hd hcenter v hsum hv
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp (t : ℂ) (ht : t ∈ Metric.closedBall τ (r / 4)) (i : Fin n) :
      (t, d + v i) ∈ Metric.ball (0, 0) r := by
    have htt : ‖t - τ‖ ≤ r / 4 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using ht
    have htn : ‖t‖ ≤ ‖t - τ‖ + ‖τ‖ := by
      simpa only [sub_add_cancel] using norm_add_le (t - τ) τ
    have hvn := norm_add_le d (v i)
    have hvi := hv i
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [Prod.mk_sub_mk, sub_zero, Prod.norm_def, max_lt_iff]
    constructor <;> linarith
  have hbase : (τ, d) ∈ Metric.ball (0, 0) r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [Prod.mk_sub_mk, sub_zero, Prod.norm_def, max_lt_iff]
    constructor <;> linarith
  have hτball : τ ∈ Metric.closedBall τ (r / 4) :=
    Metric.mem_closedBall_self (by positivity)
  have hQ : displacementSquare n v ≤ (n : ℝ) * σ ^ 2 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show ‖v i‖ ^ 2 ≤ σ ^ 2 by nlinarith [hv i, norm_nonneg (v i)])
    simpa only [displacementSquare, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hh
  have hQavg : displacementSquare n v / (n : ℝ) ≤ σ ^ 2 :=
    (div_le_iff₀ hnR).mpr (by simpa only [mul_comm] using hQ)
  let F : ℂ → ℂ := centeredPhaseAverage n g γ d v
  have hdiff (t : ℂ) (ht : t ∈ Metric.closedBall τ (r / 4)) :
      DifferentiableAt ℂ F t :=
    (centeredPhaseAverage_hasDerivAt n g γ d v t
      (fun i => (hlocal _ (hp t ht i)).1.differentiableAt)).differentiableAt
  have hclose (t : ℂ) (ht : t ∈ Metric.closedBall τ (r / 4)) :
      ‖deriv F t - c‖ ≤ ‖c‖ / 2 :=
    centeredPhaseAverage_deriv_close n g γ d c v t hn
      (fun i => (hlocal _ (hp t ht i)).1.differentiableAt)
      (fun i => (hlocal _ (hp t ht i)).2)
  have hF : ‖F τ‖ ≤ M * displacementSquare n v / (n : ℝ) :=
    centeredPhaseAverage_quadratic_bound n g γ d τ v M hcenter hsum
      (fun i => hquad (τ, d) hbase (τ, d + v i) (hp τ hτball i))
  have hsmall : ‖F τ‖ / ‖c‖ ≤ r / 16 := by
    calc
      ‖F τ‖ / ‖c‖ ≤ (M * displacementSquare n v / (n : ℝ)) / ‖c‖ :=
        div_le_div_of_nonneg_right hF hcpos.le
      _ = M * (displacementSquare n v / (n : ℝ)) / ‖c‖ := by ring
      _ ≤ M * σ ^ 2 / ‖c‖ := by gcongr
      _ ≤ M * σ / ‖c‖ := by gcongr
      _ ≤ r / 16 := (div_le_iff₀ hcpos).mpr (by nlinarith [hMσ])
  obtain ⟨t, ht, hFt, hdist, hderiv, huniq⟩ := exists_unique_zero_of_deriv_close hc
    (show 0 ≤ r / 4 by positivity) hdiff hclose (by linarith [hsmall])
  refine ⟨t, (centeredPhaseAverage_eq_zero_iff hn g γ d v t).mp hFt, ?_, ?_, hderiv, ?_⟩
  · have hh : 2 * ‖F τ‖ / ‖c‖ ≤ r / 8 := by
      calc
        2 * ‖F τ‖ / ‖c‖ = 2 * (‖F τ‖ / ‖c‖) := by ring
        _ ≤ r / 8 := by linarith
    exact hdist.trans hh
  · calc
      ‖t - τ‖ ≤ 2 * ‖F τ‖ / ‖c‖ := hdist
      _ ≤ 2 * (M * displacementSquare n v / (n : ℝ)) / ‖c‖ := by gcongr
      _ = C * displacementSquare n v / (n : ℝ) := by dsimp [C]; ring
  · intro u hu he
    exact huniq u hu ((centeredPhaseAverage_eq_zero_iff hn g γ d v u).mpr he)

end
end IsingBulk.AnisoF002.NegativeHT
