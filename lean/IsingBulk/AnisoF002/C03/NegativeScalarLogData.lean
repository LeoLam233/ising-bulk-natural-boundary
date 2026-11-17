import IsingBulk.AnisoF002.C03.NegativeCompleteDensityLog

/-!
# Constructed common scalar logarithms

The data below are proved to exist from analyticity and the two nonzero
center values.  The common radius and common constant are chosen before
the particle number; they are not new premises of the physical theorem.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.AnisoF002.Isotropic Set Filter
open scoped Topology

structure CompleteDensityScalarLogs (b : ℂ → ℂ) (γ : ℂ) where
  Lb : ℂ → ℂ
  Lh : ℂ → ℂ
  Ls : ℂ → ℂ
  Ld : ℂ → ℂ
  r : ℝ
  K : ℝ
  r_pos : 0 < r
  K_pos : 0 < K
  b_center : Lb 0 = 0
  h_center : Lh γ = 0
  s_center : Ls 0 = 0
  d_center : Ld 1 = 0
  b_analytic : AnalyticOnNhd ℂ Lb (Metric.ball 0 r)
  h_analytic : AnalyticOnNhd ℂ Lh (Metric.ball γ r)
  s_analytic : AnalyticOnNhd ℂ Ls (Metric.ball 0 r)
  d_analytic : AnalyticOnNhd ℂ Ld (Metric.ball 1 r)
  b_exp : ∀ t ∈ Metric.ball 0 r, b t ≠ 0 ∧ Complex.exp (Lb t) = b t / b 0
  h_exp : ∀ z ∈ Metric.ball γ r, Complex.sinh z ≠ 0 ∧ Complex.exp (Lh z) = Complex.sinh z / Complex.sinh γ
  s_exp : ∀ z ∈ Metric.ball 0 r, complexSinc z ≠ 0 ∧ Complex.exp (Ls z) = complexSinc z
  d_exp : ∀ z ∈ Metric.ball 1 r, z ≠ 0 ∧ Complex.exp (Ld z) = z
  b_lip : ∀ t ∈ Metric.ball 0 r, ∀ u ∈ Metric.ball 0 r, ‖Lb t - Lb u‖ ≤ K * ‖t - u‖
  h_bound : ∀ z ∈ Metric.ball γ r, ‖Lh z‖ ≤ K * ‖z - γ‖
  s_bound : ∀ z ∈ Metric.ball 0 r, ‖Ls z‖ ≤ K * ‖z‖ ^ 2
  d_bound : ∀ z ∈ Metric.ball 1 r, ‖Ld z‖ ≤ K * ‖z - 1‖

theorem exists_complete_density_scalar_logs {b : ℂ → ℂ} {γ : ℂ}
    (hb : AnalyticAt ℂ b 0) (hb0 : b 0 ≠ 0) (hγ : Complex.sinh γ ≠ 0) :
    Nonempty (CompleteDensityScalarLogs b γ) := by
  obtain ⟨Lb, rb, Kb, hrb, hKb, hLb0, hLba, hLbe, hLbb⟩ := exists_normalized_local_log hb hb0
  obtain ⟨Lh, rh, Kh, hrh, hKh, hLh0, hLha, hLhe, hLhb⟩ :=
    exists_normalized_local_log (f := Complex.sinh) Complex.analyticAt_sinh hγ
  obtain ⟨Ls, rs, Ks, hrs, hKs, hLs0, hLsa, hLse, hLsb⟩ := exists_quadratic_sinc_log
  obtain ⟨Ld, rd, Kd, hrd, hKd, hLd0, hLda, hLde, hLdb⟩ :=
    exists_normalized_local_log (f := id) (x := (1 : ℂ)) analyticAt_id one_ne_zero
  let r : ℝ := min rb (min rh (min rs rd))
  let K : ℝ := Kb + Kh + Ks + Kd + 1
  have hr : 0 < r := lt_min hrb (lt_min hrh (lt_min hrs hrd))
  have hK : 0 < K := by dsimp [K]; positivity
  have hrb' : r ≤ rb := min_le_left _ _
  have hrh' : r ≤ rh := (min_le_right _ _).trans (min_le_left _ _)
  have hrs' : r ≤ rs := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrd' : r ≤ rd := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hKb' : Kb ≤ K := by dsimp [K]; linarith
  have hKh' : Kh ≤ K := by dsimp [K]; linarith
  have hKs' : Ks ≤ K := by dsimp [K]; linarith
  have hKd' : Kd ≤ K := by dsimp [K]; linarith
  refine ⟨{
    Lb := Lb, Lh := Lh, Ls := Ls, Ld := Ld, r := r, K := K,
    r_pos := hr, K_pos := hK,
    b_center := hLb0, h_center := hLh0, s_center := hLs0, d_center := hLd0,
    b_analytic := hLba.mono (Metric.ball_subset_ball hrb'),
    h_analytic := hLha.mono (Metric.ball_subset_ball hrh'),
    s_analytic := hLsa.mono (Metric.ball_subset_ball hrs'),
    d_analytic := hLda.mono (Metric.ball_subset_ball hrd'),
    b_exp := fun t ht => hLbe t (Metric.ball_subset_ball hrb' ht),
    h_exp := fun z hz => hLhe z (Metric.ball_subset_ball hrh' hz),
    s_exp := fun z hz => hLse z (Metric.ball_subset_ball hrs' hz),
    d_exp := ?_, b_lip := ?_, h_bound := ?_, s_bound := ?_, d_bound := ?_
  }⟩
  · intro z hz
    simpa only [id_eq, div_one] using hLde z (Metric.ball_subset_ball hrd' hz)
  · intro t ht u hu
    exact (hLbb u (Metric.ball_subset_ball hrb' hu) t (Metric.ball_subset_ball hrb' ht)).trans
      (mul_le_mul_of_nonneg_right hKb' (norm_nonneg _))
  · intro z hz
    have hh := hLhb γ (Metric.mem_ball_self hrh) z (Metric.ball_subset_ball hrh' hz)
    rw [hLh0, sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hKh' (norm_nonneg _))
  · intro z hz
    exact (hLsb z (Metric.ball_subset_ball hrs' hz)).trans
      (mul_le_mul_of_nonneg_right hKs' (sq_nonneg _))
  · intro z hz
    have hh := hLdb 1 (Metric.mem_ball_self hrd) z (Metric.ball_subset_ball hrd' hz)
    rw [hLd0, sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hKd' (norm_nonneg _))

theorem normalized_log_relative_factor {b L : ℂ → ℂ} {τ t : ℂ}
    (hb0 : b 0 ≠ 0) (hτ : b τ ≠ 0)
    (heτ : Complex.exp (L τ) = b τ / b 0) (het : Complex.exp (L t) = b t / b 0) :
    b t = b τ * Complex.exp (L t - L τ) := by
  rw [Complex.exp_sub, het, heτ]
  field_simp

end
end IsingBulk.AnisoF002.NegativeHT
