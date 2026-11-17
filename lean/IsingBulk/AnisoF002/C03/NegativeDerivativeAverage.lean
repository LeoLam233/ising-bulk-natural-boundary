import IsingBulk.AnisoF002.C03.NegativeDensityLogBounds

/-!
# The complete phase-derivative denominator

The linear angular terms cancel in the full sum of temperature
derivatives on the zero-sum plane.  All constants come from the single
fixed analytic phase, before the number of particles is chosen.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem analytic_joint_uniform_estimates {H : ℂ × ℂ → ℂ}
    (hH : AnalyticAt ℂ H (0, 0)) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ AnalyticOnNhd ℂ H (Metric.ball (0, 0) r) ∧
      (∀ p ∈ Metric.ball (0, 0) r, ‖fderiv ℂ H p‖ ≤ M) ∧
      ∀ p ∈ Metric.ball (0, 0) r, ∀ q ∈ Metric.ball (0, 0) r,
        ‖H q - H p - fderiv ℂ H p (q - p)‖ ≤ M * ‖q - p‖ ^ 2 := by
  let M : ℝ := ‖fderiv ℂ H (0, 0)‖ + ‖fderiv ℂ (fderiv ℂ H) (0, 0)‖ + 2
  have hM : 0 < M := by dsimp [M]; positivity
  have hb₁ : ∀ᶠ p in 𝓝 (0, 0), ‖fderiv ℂ H p‖ < M :=
    hH.fderiv.continuousAt.norm.eventually (Iio_mem_nhds (by
      dsimp [M]; linarith [norm_nonneg (fderiv ℂ (fderiv ℂ H) (0, 0))]))
  have hb₂ : ∀ᶠ p in 𝓝 (0, 0), ‖fderiv ℂ (fderiv ℂ H) p‖ < M :=
    hH.fderiv.fderiv.continuousAt.norm.eventually (Iio_mem_nhds (by
      dsimp [M]; linarith [norm_nonneg (fderiv ℂ H (0, 0))]))
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.mp
    (hH.eventually_analyticAt.and (hb₁.and hb₂))
  have ha (p : ℂ × ℂ) (hp : p ∈ Metric.ball (0, 0) r) := hh (Metric.mem_ball.mp hp)
  have hLip (p : ℂ × ℂ) (hp : p ∈ Metric.ball (0, 0) r)
      (q : ℂ × ℂ) (hq : q ∈ Metric.ball (0, 0) r) :
      ‖fderiv ℂ H q - fderiv ℂ H p‖ ≤ M * ‖q - p‖ :=
    (convex_ball (0 : ℂ × ℂ) r).norm_image_sub_le_of_norm_fderiv_le
      (fun a ha' => (ha a ha').1.fderiv.differentiableAt)
      (fun a ha' => (ha a ha').2.2.le) hp hq
  refine ⟨r, M, hr, hM, (fun p hp => (ha p hp).1),
    (fun p hp => (ha p hp).2.1.le), ?_⟩
  intro p hp q hq
  have hs := (convex_ball (0 : ℂ × ℂ) r).segment_subset hp hq
  have hb : ∀ a ∈ segment ℝ p q, ‖fderiv ℂ H a - fderiv ℂ H p‖ ≤ M * ‖q - p‖ := by
    intro a ha'
    exact (hLip p hp a (hs ha')).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment ha') hM.le)
  have he := (convex_segment p q).norm_image_sub_le_of_norm_fderiv_le'
    (fun a ha' => (ha a (hs ha')).1.differentiableAt) hb
    (left_mem_segment ℝ p q) (right_mem_segment ℝ p q)
  simpa only [pow_two, mul_assoc] using he

theorem exists_averaged_zero_sum_shift_bound {H : ℂ × ℂ → ℂ}
    (hH : AnalyticAt ℂ H (0, 0)) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      ∀ n : ℕ, 0 < n → ∀ τ d t : ℂ, ∀ v : Fin n → ℂ,
        (∑ i, v i) = 0 → (τ, d) ∈ Metric.ball (0, 0) r →
        (t, d) ∈ Metric.ball (0, 0) r →
        (∀ i, (t, d + v i) ∈ Metric.ball (0, 0) r) →
        ‖(∑ i, H (t, d + v i)) / (n : ℂ) - H (τ, d)‖ ≤
          M * (‖t - τ‖ + displacementSquare n v / (n : ℝ)) := by
  obtain ⟨r, M, hr, hM, ha, hfd, hquad⟩ := analytic_joint_uniform_estimates hH
  refine ⟨r, M, hr, hM, ?_⟩
  intro n hn τ d t v hsum hp hq hv
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have htime : ‖H (t, d) - H (τ, d)‖ ≤ M * ‖t - τ‖ := by
    simpa [Prod.norm_def] using
      (convex_ball (0 : ℂ × ℂ) r).norm_image_sub_le_of_norm_fderiv_le
        (fun p hp' => (ha p hp').differentiableAt) hfd hp hq
  have hspace := centeredPhaseAverage_quadratic_bound n H (H (t, d)) d t v M rfl hsum
    (fun i => hquad (t, d) hq (t, d + v i) (hv i))
  have he : centeredPhaseAverage n H (H (t, d)) d v t =
      (∑ i, H (t, d + v i)) / (n : ℂ) - H (t, d) := by
    unfold centeredPhaseAverage
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [he] at hspace
  calc
    _ = ‖((∑ i, H (t, d + v i)) / (n : ℂ) - H (t, d)) + (H (t, d) - H (τ, d))‖ := by congr 1; ring
    _ ≤ ‖(∑ i, H (t, d + v i)) / (n : ℂ) - H (t, d)‖ + ‖H (t, d) - H (τ, d)‖ := norm_add_le _ _
    _ ≤ M * displacementSquare n v / (n : ℝ) + M * ‖t - τ‖ := add_le_add hspace htime
    _ = M * (‖t - τ‖ + displacementSquare n v / (n : ℝ)) := by ring

def phaseTemperatureDerivative (g : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  fderiv ℂ g p (1, 0)

theorem phaseTemperatureDerivative_analyticAt {g : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (hg : AnalyticAt ℂ g p) : AnalyticAt ℂ (phaseTemperatureDerivative g) p :=
  ((ContinuousLinearMap.apply ℂ ℂ ((1, 0) : ℂ × ℂ)).analyticAt _).comp hg.fderiv

theorem exists_phase_derivative_ratio_bound {g : ℂ × ℂ → ℂ}
    (hg : AnalyticAt ℂ g (0, 0)) (hc : phaseTemperatureDerivative g (0, 0) ≠ 0) :
    ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
      ∀ n : ℕ, 0 < n → ∀ τ d t : ℂ, ∀ v : Fin n → ℂ,
        (∑ i, v i) = 0 → (τ, d) ∈ Metric.ball (0, 0) r →
        (t, d) ∈ Metric.ball (0, 0) r →
        (∀ i, (t, d + v i) ∈ Metric.ball (0, 0) r) →
        phaseTemperatureDerivative g (τ, d) ≠ 0 ∧
        ‖phaseTemperatureSum n g d t v /
          ((n : ℂ) * phaseTemperatureDerivative g (τ, d)) - 1‖ ≤
            K * (‖t - τ‖ + displacementSquare n v / (n : ℝ)) := by
  let H := phaseTemperatureDerivative g
  have hH : AnalyticAt ℂ H (0, 0) := phaseTemperatureDerivative_analyticAt hg
  obtain ⟨r, M, hr, hM, hb⟩ := exists_averaged_zero_sum_shift_bound hH
  have hcpos : 0 < ‖H (0, 0)‖ := norm_pos_iff.mpr hc
  have hclose : ∀ᶠ p in 𝓝 (0, 0), ‖H p - H (0, 0)‖ < ‖H (0, 0)‖ / 2 :=
    (hH.continuousAt.sub_const _).norm.eventually
      (Iio_mem_nhds (by simpa only [sub_self, norm_zero] using half_pos hcpos))
  obtain ⟨s, hs, hsn⟩ := Metric.eventually_nhds_iff.mp hclose
  let R : ℝ := min r s
  let K : ℝ := M / (‖H (0, 0)‖ / 2)
  have hR : 0 < R := lt_min hr hs
  have hRr : Metric.ball (0 : ℂ × ℂ) R ⊆ Metric.ball 0 r := Metric.ball_subset_ball (min_le_left _ _)
  have hRs : Metric.ball (0 : ℂ × ℂ) R ⊆ Metric.ball 0 s := Metric.ball_subset_ball (min_le_right _ _)
  have hK : 0 < K := div_pos hM (half_pos hcpos)
  refine ⟨R, K, hR, hK, ?_⟩
  intro n hn τ d t v hsum hp hq hv
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcen : ‖H (0, 0)‖ / 2 ≤ ‖H (τ, d)‖ := by
    have hh := hsn (Metric.mem_ball.mp (hRs hp))
    have hn' := norm_sub_norm_le (H (0, 0)) (H (τ, d))
    rw [norm_sub_rev] at hn'
    linarith
  have hcn : H (τ, d) ≠ 0 := norm_pos_iff.mp ((half_pos hcpos).trans_le hcen)
  refine ⟨hcn, ?_⟩
  have he : phaseTemperatureSum n g d t v / ((n : ℂ) * H (τ, d)) - 1 =
      ((∑ i, H (t, d + v i)) / (n : ℂ) - H (τ, d)) / H (τ, d) := by
    unfold phaseTemperatureSum
    change (∑ i, H (t, d + v i)) / ((n : ℂ) * H (τ, d)) - 1 = _
    field_simp
  rw [he, norm_div]
  have havg := hb n hn τ d t v hsum (hRr hp) (hRr hq) (fun i => hRr (hv i))
  have hnon : 0 ≤ ‖t - τ‖ + displacementSquare n v / (n : ℝ) :=
    add_nonneg (norm_nonneg _) (div_nonneg (displacementSquare_nonneg n v) (Nat.cast_nonneg n))
  calc
    _ ≤ (M * (‖t - τ‖ + displacementSquare n v / (n : ℝ))) / ‖H (τ, d)‖ :=
      div_le_div_of_nonneg_right havg (norm_nonneg _)
    _ ≤ (M * (‖t - τ‖ + displacementSquare n v / (n : ℝ))) / (‖H (0, 0)‖ / 2) := by
      gcongr
    _ = K * (‖t - τ‖ + displacementSquare n v / (n : ℝ)) := by dsimp [K]; ring

end
end IsingBulk.AnisoF002.NegativeHT
